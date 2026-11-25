/*
 *  Copyright 2025 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.xcfa.analysis.refinery

import hu.bme.mit.theta.analysis.algorithm.refinery.MemoryAllocationExpr
import hu.bme.mit.theta.analysis.algorithm.refinery.MemoryDeallocationExpr
import hu.bme.mit.theta.analysis.algorithm.refinery.RefineryCell
import hu.bme.mit.theta.analysis.algorithm.refinery.RefineryObjectType
import hu.bme.mit.theta.analysis.algorithm.refinery.RefineryPointerType
import hu.bme.mit.theta.analysis.algorithm.refinery.RefineryRule
import hu.bme.mit.theta.analysis.algorithm.refinery.RefineryStaticObject
import hu.bme.mit.theta.analysis.algorithm.refinery.RefineryTransitionRuleBuilder
import hu.bme.mit.theta.analysis.algorithm.refinery.RefineryTransitionSystemBuilder
import hu.bme.mit.theta.analysis.algorithm.refinery.RefineryTransitionSystemBuilder.Companion.refinerified
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.abstracttype.AddExpr
import hu.bme.mit.theta.core.type.abstracttype.PosExpr
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.IteExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.UnsupportedFrontendElementException
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.MemoryModelType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CVoid
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CStruct
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.ObjectLayout
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger
import hu.bme.mit.theta.frontend.transformation.model.types.complex.real.CReal
import java.math.BigInteger
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel
import hu.bme.mit.theta.xcfa.utils.POINTER_BASE_CLASSES
import hu.bme.mit.theta.xcfa.utils.multiAllocationSeed
import hu.bme.mit.theta.xcfa.utils.staticBaseLimit
import hu.bme.mit.theta.xcfa.utils.getAllLabels

class XcfaRefineryTransitionSystemBuilder(
  xcfa: XCFA,
  parseContext: ParseContext,
  property: ErrorDetection,
) : RefineryTransitionSystemBuilder() {

  companion object {
    internal const val LOCATION_ENUM = "Location"
    internal const val LOCATION_DECLARATION = "loc"
  }

  init {
    check(xcfa.initProcedures.size == 1) { "XCFA must have exactly one initial procedure." }
    check(property == ErrorDetection.ERROR_LOCATION) {
      "The Refinery backend does not encode the $property property yet."
    }
    // The layouts below assume a struct or array member is a separate sub-object.
    check(parseContext.memoryModel == MemoryModelType.multi) {
      "The Refinery backend supports only the multi memory model."
    }
  }

  private val procedure = xcfa.initProcedures.first().first

  private val types = XcfaRefineryTypes(parseContext)

  override val initialNextAddress: BigInteger =
    BigInteger.valueOf(
      multiAllocationSeed(staticBaseLimit(parseContext.staticObjectTypes.keys.map { it.toInt() }))
        .toLong()
    )

  private val allocationSizes =
    procedure.edges
      .flatMap { it.getAllLabels() }
      .mapNotNull { label ->
        when {
          label is InvokeLabel && label.name == "malloc" -> (label.params[1] as? IntLitExpr)?.value
          label is StmtLabel ->
            ((label.stmt as? AssignStmt<*>)?.expr as? MemoryAllocationExpr<*>)?.size
          else -> null
        }
      }
      .toSet()

  private val pointers =
    procedure.vars
      .filter {
        val cType = parseContext.metadata.getMetadataValue(it.ref, "cType")
        cType.isPresent && cType.get() is CPointer
      }
      .toSet()

  private val locations: MutableSet<String> = mutableSetOf()

  private val locationDeclaration: String
    get() =
      """
      |enum $LOCATION_ENUM {
      |    ${locations.joinToString(", ")}
      |}
      """
        .trimMargin()

  override val environmentDeclarations: List<String> // add program counter (xcfa location)
    get() = listOf("pred $LOCATION_DECLARATION($LOCATION_ENUM l).") + super.environmentDeclarations

  override val environmentSetup: String
    get() = listOf(locationDeclaration, super.environmentSetup).joinToString("\n\n")

  override val initialStateDeclarations: List<String>
    get() =
      buildList {
        addAll(super.initialStateDeclarations)
        addAll(
          listOf(
            "$LOCATION_DECLARATION(${procedure.initLoc.name.refinerified}).",
            "default !$LOCATION_DECLARATION(*).",
            "scope NamedPointer += 0.",
          )
        )
        variables.mapTo(this) { "${it.name.refinerified}(): 0." }
        addAll(xcfaTransitionBuilder.staticObjectDeclarations())
        pointers.flatMapTo(this) {
          val name = it.name.refinerified
          val pointer = "pointer_$name"
          listOf(
            "atom $name.",
            "NamedPointer($name).",
            "pointer($name, $pointer).",
            "target($pointer, null).",
            "offset($pointer): 0.",
            "MemoryObject::size($pointer): 4.", // C pointer size
          )
        }
      }

  private val xcfaTransitionBuilder =
    XcfaRefineryTransitionRuleBuilder(locations, variables, pointers, allocationSizes, types)

  override val transitions: List<RefineryRule> =
    xcfa.initProcedures.first().first.edges.flatMap { edge -> xcfaTransitionBuilder.build(edge) }

  override val targetProperties: List<String> =
    when (property) {
      ErrorDetection.ERROR_LOCATION ->
        listOf(
          "$LOCATION_DECLARATION(${procedure.errorLoc.get().name.refinerified})"
        )
      ErrorDetection.MEMSAFETY -> listOf("invalidDeref()", "invalidFree()", "invalidMemtrack()")
      else -> error("The Refinery backend does not encode the $property property.")
    }
}

/** The Refinery view of C types: object layouts and the global objects of a program. */
class XcfaRefineryTypes(val parseContext: ParseContext) {

  /** The type a pointer into the global object of type [type] has. */
  fun staticPointee(type: CComplexType): CComplexType = if (type is CArray) type.embeddedType else type

  /** Every global object at its compile-time address. */
  val staticObjects: Map<BigInteger, RefineryStaticObject> =
    parseContext.staticObjectTypes.mapValues { (_, type) ->
      val count =
        if (type is CArray) {
          ObjectLayout.constantDimension(type)
            ?: throw UnsupportedFrontendElementException("Global array without a constant size")
        } else 1
      RefineryStaticObject(staticPointee(type).refineryObjectType(), count)
    }

  fun refineryObjectType(type: CComplexType): RefineryObjectType = type.refineryObjectType()

  @JvmName("toRefineryObjectType")
  private fun CComplexType.refineryObjectType(): RefineryObjectType =
    when (this) {
      is CPointer -> RefineryObjectType("ptr", sizeInBytes(), RefineryCell.Pointer)
      is CArray -> {
        val count =
          ObjectLayout.constantDimension(this)
            ?: throw UnsupportedFrontendElementException("Array without a constant size: $this")
        val element = embeddedType.refineryObjectType()
        RefineryObjectType(
          "${element.id}[$count]",
          element.sizeBytes * BigInteger.valueOf(count.toLong()),
          RefineryCell.SubObject(List(count) { element }, isArray = true),
        )
      }
      is CStruct -> {
        if (isUnion) throw UnsupportedFrontendElementException("Unions are not supported: $this")
        val members = fields.map { it.get2().refineryObjectType() }
        // Packed bitfields share a cell, which breaks the one-part-per-member layout.
        if (fields.withIndex().any { (index, field) -> unitOffsetOf(field.get1()) != index }) {
          throw UnsupportedFrontendElementException("Bitfields are not supported: $this")
        }
        val id = fields.zip(members).joinToString(",", "{", "}") { (f, m) -> "${f.get1()}:${m.id}" }
        RefineryObjectType(id, sizeInBytes(), RefineryCell.SubObject(members, isArray = false))
      }
      is CReal -> throw UnsupportedFrontendElementException("Floats are not supported: $this")
      is CInteger -> RefineryObjectType(typeName, sizeInBytes(), RefineryCell.Value)
      else -> throw UnsupportedFrontendElementException("Unsupported pointee type: $this")
    }

  private fun CComplexType.sizeInBytes(): BigInteger =
    BigInteger.valueOf(ObjectLayout.sizeofBytes(this, parseContext.architecture).toLong())
}

class XcfaRefineryTransitionRuleBuilder(
  private val locations: MutableSet<String>,
  variables: MutableSet<Decl<*>>,
  pointers: Set<Decl<*>>,
  allocationSizes: Set<BigInteger>,
  private val types: XcfaRefineryTypes,
) :
  RefineryTransitionRuleBuilder<XcfaEdge>(
    variables,
    pointers,
    allocationSizes,
    types.staticObjects,
    POINTER_BASE_CLASSES,
  ) {

  private val parseContext = types.parseContext

  override fun pointerTypeOf(expr: Expr<*>): RefineryPointerType {
    if (expr is IntLitExpr && expr.value in parseContext.staticObjectTypes) {
      return RefineryPointerType.Typed(types.staticObjects.getValue(expr.value).pointee)
    }
    if (expr is LitExpr<*>) return RefineryPointerType.Untyped // a null pointer constant
    // A cast changes no memory: the pointed region keeps the type of the cast's operand.
    if (expr is PosExpr<*>) return pointerTypeOf(expr.op)
    val type = cTypeOf(expr) as? CPointer ?: return RefineryPointerType.NotPointer
    val pointee = type.embeddedType
    return if (pointee is CVoid) RefineryPointerType.Untyped
    else RefineryPointerType.Typed(types.refineryObjectType(pointee))
  }

  private fun cTypeOf(expr: Expr<*>): CComplexType {
    // A dereference's own stamp is not reliable after the passes, its base pointer's type is.
    if (expr is Dereference<*, *, *>) return dereferencedType(expr)
    if (expr is IntLitExpr) {
      parseContext.staticObjectTypes[expr.value]?.let {
        return CPointer(null, types.staticPointee(it), parseContext)
      }
    }
    val metadata = { e: Expr<*> ->
      parseContext.metadata.getMetadataValue(e, "cType").orElse(null) as CComplexType?
    }
    return metadata(expr)
      ?: when (expr) {
        is RefExpr<*> -> metadata(expr.decl.ref)
        is AddExpr<*> -> expr.ops.map { cTypeOf(it) }.firstOrNull { it is CPointer }
        is IteExpr<*> -> cTypeOf(expr.then)
        else -> null
      }
      ?: error("No C type is known for $expr.")
  }

  /**
   * A struct's members are the cells of the region its pointer points to, indexed by member. A
   * cell of a struct or array stored by value holds a pointer to its sub-object.
   */
  private fun dereferencedType(deref: Dereference<*, *, *>): CComplexType {
    val pointee =
      when (val base = cTypeOf(deref.array)) {
        is CPointer -> base.embeddedType
        is CArray -> base.embeddedType
        else -> error("Dereference of non-pointer $base in $deref.")
      }
    val cell =
      if (pointee !is CStruct) pointee
      else {
        val index =
          (deref.offset as? IntLitExpr)?.value?.toInt()
            ?: throw UnsupportedFrontendElementException(
              "Struct member at a non-constant offset: $deref"
            )
        pointee.fields.getOrNull(index)?.get2()
          ?: error("No member at offset $index of $pointee in $deref.")
      }
    return when {
      cell is CArray -> CPointer(null, cell.embeddedType, parseContext)
      cell is CStruct && !cell.isUnion -> CPointer(null, cell, parseContext)
      else -> cell
    }
  }

  companion object {
    private val XcfaLabel.supported: Boolean
      get() =
        this::class in
          setOf(StmtLabel::class, NopLabel::class, SequenceLabel::class, NondetLabel::class) ||
          (this is InvokeLabel && this.name in listOf("malloc"))
  }

  private val loc = XcfaRefineryTransitionSystemBuilder.LOCATION_DECLARATION
  @Suppress("PrivatePropertyName")
  private val Location = XcfaRefineryTransitionSystemBuilder.LOCATION_ENUM

  override fun build(transition: XcfaEdge): Set<RefineryRule> {
    check(transition.getAllLabels().all { it.supported }) {
      "Unsupported XCFA label found in XCFA->Refinery transition: ${transition.label}"
    }
    val sourceLocName = transition.source.name.refinerified
    val targetLocName = transition.target.name.refinerified
    val name = "${sourceLocName}__to__${targetLocName}"
    val label = transition.label.replaceInvokes()
    val topRule = label.toStmt().toRules()
    topRule.setIds()
    return topRule.allRules
      .mapIndexed { index, rule ->
        val source = if (rule.preId == topRule.preId) sourceLocName else "${name}__${rule.preId}"
        val target = if (rule.postId == topRule.postId) targetLocName else "${name}__${rule.postId}"
        locations.add(source)
        locations.add(target)
        val locPrecondition = "$loc($Location::$source)"
        val locActions =
          listOfNotNull(
            if (source != target) "!$loc($Location::$source)" else null,
            "$loc($Location::$target)",
          )
        rule
          .copy(
            preConditionClauses = setOf(locPrecondition) + rule.preConditionClauses,
            actionLiterals = rule.actionLiterals + locActions,
          )
          .toRefineryRule("${name}__$index")
      }
      .toSet()
  }

  private fun XcfaLabel.replaceInvokes(): XcfaLabel =
    when (this) {
      is InvokeLabel ->
        when (name) {
          "malloc" -> {
            val ret = (params[0] as RefExpr).decl as VarDecl
            val size = (params[1] as? IntLitExpr)?.value
            AssignStmtLabel(ret, MemoryAllocationExpr(size, ret.type), metadata)
          }
          "free" -> {
            val ret = (params[0] as RefExpr).decl as VarDecl
            AssignStmtLabel(ret, MemoryDeallocationExpr(params[1]), metadata)
          }
          else -> error("Unsupported invoke label: $this")
        }
      is SequenceLabel -> SequenceLabel(labels.map { it.replaceInvokes() }, metadata)
      is NondetLabel -> NondetLabel(labels.map { it.replaceInvokes() }.toSet(), metadata)
      else -> this
    }
}
