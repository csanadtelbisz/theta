/*
 *  Copyright 2025-2026 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.algorithm.refinery

import hu.bme.mit.theta.analysis.algorithm.refinery.RefineryTransitionRuleBuilder.RefineryExpr.ExprType.NON_POINTER
import hu.bme.mit.theta.analysis.algorithm.refinery.RefineryTransitionRuleBuilder.RefineryExpr.ExprType.POINTER
import hu.bme.mit.theta.analysis.algorithm.refinery.RefineryTransitionSystemBuilder.Companion.refinerified
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.stmt.*
import hu.bme.mit.theta.core.type.*
import hu.bme.mit.theta.core.type.abstracttype.AddExpr
import hu.bme.mit.theta.core.type.abstracttype.EqExpr
import hu.bme.mit.theta.core.type.abstracttype.ModExpr
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr
import hu.bme.mit.theta.core.type.abstracttype.PosExpr
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.IteExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.AndExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Or
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr
import hu.bme.mit.theta.core.type.booltype.NotExpr
import hu.bme.mit.theta.core.type.booltype.OrExpr
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import java.math.BigInteger
import java.util.IdentityHashMap

data class RefineryRule(
  val name: String,
  val parameters: List<Pair<String, String>> = listOf(),
  val preConditionClauses: Set<String>,
  val actionLiterals: List<String>,
) {

  init {
    check(actionLiterals.isNotEmpty()) { "Action clauses cannot be empty in a Refinery rule." }
  }

  override fun toString(): String =
    """
    |transition rule $name(${parameters.joinToString(", ") { "${it.first} ${it.second}" }}) <->
    |    ${
      if (preConditionClauses.isEmpty()) "true"
      else preConditionClauses.joinToString(",\n    ")
    }
    |==>
    |    ${actionLiterals.joinToString(",\n    ")}.
    """
      .trimMargin()
}

/** A C object type as laid out in Refinery: [id] tells types apart, [sizeBytes] is its `sizeof`. */
data class RefineryObjectType(val id: String, val sizeBytes: BigInteger, val cell: RefineryCell)

/** The memory part holding one object of a [RefineryObjectType]. */
sealed interface RefineryCell {

  val className: String

  data object Value : RefineryCell {
    override val className = "Value"
  }

  data object Pointer : RefineryCell {
    override val className = "Pointer"
  }

  /**
   * A struct or array stored by value: the part points to a sub-object region of [members]. A
   * pointer into an array's region has the element type, so that is the region's type then.
   */
  data class SubObject(val members: List<RefineryObjectType>, val isArray: Boolean) : RefineryCell {
    override val className = "Pointer"

    init {
      check(members.isNotEmpty()) { "A sub-object must have at least one member." }
    }
  }
}

/**
 * A global object at a compile-time address: [count] consecutive objects of [pointee], the type a
 * pointer into it has (a struct's own type, or an array's element type).
 */
data class RefineryStaticObject(val pointee: RefineryObjectType, val count: Int)

/** The C type of a pointer-valued expression, as far as the memory it points to is concerned. */
sealed interface RefineryPointerType {

  data object NotPointer : RefineryPointerType

  /** `void *` or a null pointer constant: the pointed memory gets no type from it. */
  data object Untyped : RefineryPointerType

  data class Typed(val pointee: RefineryObjectType) : RefineryPointerType
}

/**
 * Builds Refinery transition rules from statements. Memory regions are created untyped by an
 * allocation and get their parts once a typed pointer first points into them: subclasses supply
 * the C types through [pointerTypeOf].
 *
 * Global objects are regions of the initial state at their compile-time addresses
 * ([staticObjects]); such an address literal denotes a constant pointer to the region. Each new
 * region takes the address `next_address + addressStep` and advances `next_address` by
 * [addressStep], as the allocation counter of the other analyses does.
 */
abstract class RefineryTransitionRuleBuilder<T>(
  protected val variables: MutableSet<Decl<*>>,
  protected val pointers: Set<Decl<*>>,
  private val allocationSizes: Set<BigInteger>,
  private val staticObjects: Map<BigInteger, RefineryStaticObject>,
  private val addressStep: Int,
) {

  companion object {

    val supportedOperators =
      setOf("+", "-", "*", "/", "==", "!=", "<", "<=", ">", ">=", "!", "&&", "||")

    const val UNSUPPORTED_FEATURE = "unsupportedFeature"

    /** The `InvalidMemory` atom: the target of a null or not yet written pointer. */
    const val INVALID_MEMORY = "null"

    private const val UNSUPPORTED_ACTION = "$UNSUPPORTED_FEATURE()"

    /** Larger regions would need a transition rule with as many new objects as parts. */
    private const val MAX_INTERPRETED_PARTS = 64
  }

  /** The C type of the pointer [expr], or [RefineryPointerType.NotPointer] for other values. */
  protected abstract fun pointerTypeOf(expr: Expr<*>): RefineryPointerType

  private val typeIds = mutableMapOf<String, Int>()

  private fun typeId(type: RefineryObjectType): Int = typeIds.getOrPut(type.id) { typeIds.size }

  /**
   * The parts of a [size]-byte region a [type] pointer points to, or null if unsupported. A pointer
   * to a struct indexes its members, so only a single struct is supported.
   */
  private fun regionParts(size: BigInteger, type: RefineryObjectType): List<RefineryObjectType>? {
    if (size.signum() <= 0 || type.sizeBytes.signum() <= 0) return null
    val (count, remainder) = size.divideAndRemainder(type.sizeBytes)
    if (remainder.signum() != 0 || count > BigInteger.valueOf(MAX_INTERPRETED_PARTS.toLong())) {
      return null
    }
    return when (val cell = type.cell) {
      is RefineryCell.SubObject -> if (count == BigInteger.ONE) cell.members else null
      else -> List(count.toInt()) { type }
    }
  }

  /** The address of the [index]th region a rule creates (counting from 1). */
  private fun newRegionAddress(index: Int): String =
    "next_address() + ${addressStep * index}"

  /** The constant pointer an address literal of a global object denotes. */
  protected fun staticPointer(address: BigInteger): String = "static_pointer_$address"

  /** The initial-state assertions of the global objects' regions. */
  fun staticObjectDeclarations(): List<String> =
    staticObjects.flatMap { (address, obj) ->
      val region = "static_region_$address"
      val partTypes =
        when (val cell = obj.pointee.cell) {
          is RefineryCell.SubObject ->
            if (obj.count == 1 && !cell.isArray) cell.members
            else error("Unsupported global object layout at $address: ${obj.pointee.id}")
          else -> List(obj.count) { obj.pointee }
        }
      // Aggregate members are global objects of their own, the initialization points the cell to it.
      val parts =
        partTypes.flatMapIndexed { offset, type ->
          val part = "static_part_${address}_$offset"
          listOf(
            "atom $part.",
            "${type.cell.className}($part).",
            *(if (type.cell is RefineryCell.Pointer) arrayOf("target($part, $INVALID_MEMORY).")
            else arrayOf()),
            "parts($region, $part).",
            "offset($part): $offset.",
          )
        }
      listOf(
        "atom $region.",
        "MemoryRegion($region).",
        "MemoryRegion::address($region): $address.",
        "MemoryRegion::size($region): ${obj.pointee.sizeBytes * BigInteger.valueOf(obj.count.toLong())}.",
        "valid($region).",
        "interpreted($region).",
        "dataType($region): ${typeId(obj.pointee)}.",
      ) +
        parts +
        listOf(
          "atom ${staticPointer(address)}.",
          "ConstantPointer(${staticPointer(address)}).",
          "target(${staticPointer(address)}, static_part_${address}_0).",
        )
    }

  /** Collects the new objects and actions that create the parts of uninterpreted regions. */
  private inner class RegionInterpreter(private var newRegions: Int) {
    val parameters = mutableListOf<Pair<String, String>>()
    val actions = mutableListOf<String>()
    private var counter = 0

    /**
     * Fills [region] of a [type] pointer with [parts] and returns the offset-0 part. An existing
     * [base] part is reused at offset 0 and only gets its class.
     */
    fun interpret(
      region: String,
      type: RefineryObjectType,
      parts: List<RefineryObjectType>,
      base: String?,
    ): String = fill(region, type, parts, base)

    val addressActions: List<String>
      get() =
        if (newRegions == 0) listOf()
        else listOf("next_address(): ${newRegionAddress(newRegions)}")

    private fun fill(
      region: String,
      regionType: RefineryObjectType,
      parts: List<RefineryObjectType>,
      base: String?,
    ): String {
      actions += "interpreted($region)"
      actions += "dataType($region): ${typeId(regionType)}"
      return parts
        .mapIndexed { offset, type ->
          val part =
            if (offset == 0 && base != null) base.also { actions += "${type.cell.className}($it)" }
            else "part_${counter++}".also { parameters += "@new ${type.cell.className}" to it }
          actions += "parts($region, $part)"
          actions += "offset($part): $offset"
          val cell = type.cell
          if (cell is RefineryCell.SubObject) {
            val subRegion = "sub_region_${counter++}"
            parameters += "@new MemoryRegion" to subRegion
            actions +=
              listOf(
                "MemoryRegion::address($subRegion): ${newRegionAddress(++newRegions)}",
                "MemoryRegion::size($subRegion): ${type.sizeBytes}",
                "valid($subRegion)",
              )
            val subType = if (cell.isArray) cell.members.first() else type
            actions += "target($part, ${fill(subRegion, subType, cell.members, null)})"
          } else if (cell is RefineryCell.Pointer) {
            // An unknown target would let every later store enumerate each node as the old one.
            actions += "target($part, $INVALID_MEMORY)"
          }
          part
        }
        .first()
    }
  }

  /** One way of storing a pointer, with the region instrumentation it needs. */
  private data class StoreVariant(
    val parameters: List<Pair<String, String>> = listOf(),
    val preconditions: Set<String> = setOf(),
    val actions: List<String> = listOf(),
    val retarget: Boolean = true,
  )

  /**
   * The variants of storing a pointer to [target] from a [source]-typed pointer into a
   * [destination]-typed one. Storing an untyped pointer into a typed one interprets the region the
   * first time; a region already interpreted with another type is an unsupported reinterpretation.
   */
  private fun storeVariants(
    destination: Expr<*>,
    source: Expr<*>,
    target: String,
  ): List<StoreVariant> {
    val destinationType = pointerTypeOf(destination)
    check(destinationType != RefineryPointerType.NotPointer) {
      "Pointer stored into non-pointer $destination."
    }
    if (destinationType !is RefineryPointerType.Typed) return listOf(StoreVariant())
    val type = destinationType.pointee
    when (val sourceType = pointerTypeOf(source)) {
      is RefineryPointerType.Typed -> {
        check(sourceType.pointee.id == type.id) {
          "Unsupported pointer conversion from $source to $destination: memory reinterpretation is not supported."
        }
        return listOf(StoreVariant())
      }
      RefineryPointerType.NotPointer -> error("Non-pointer $source stored as a pointer.")
      RefineryPointerType.Untyped -> {}
    }

    val region = "stored_region"
    val regionParameter = listOf("MemoryRegion" to region)
    val inRegion = setOf("parts($region, $target)")
    val interpreted = inRegion + "interpreted($region)"
    val uninterpreted = inRegion + "!interpreted($region)"
    val id = typeId(type)
    val unsupported = { preconditions: Set<String> ->
      StoreVariant(regionParameter, preconditions, listOf(UNSUPPORTED_ACTION), retarget = false)
    }
    return buildList {
      add(StoreVariant(preconditions = setOf("!parts(_, $target)")))
      add(StoreVariant(regionParameter, interpreted + "dataType($region) == $id"))
      add(unsupported(interpreted + "dataType($region) != $id"))
      for (size in allocationSizes) {
        val sized = uninterpreted + "MemoryRegion::size($region) == $size"
        val parts = regionParts(size, type)
        if (parts == null) {
          add(unsupported(sized))
        } else {
          val interpreter = RegionInterpreter(0)
          interpreter.interpret(region, type, parts, target)
          add(
            StoreVariant(
              regionParameter + interpreter.parameters,
              sized,
              interpreter.actions + interpreter.addressActions,
            )
          )
        }
      }
      add(unsupported(uninterpreted + allocationSizes.map { "MemoryRegion::size($region) != $it" }))
    }
  }

  private fun storeRules(
    pointer: String,
    target: String,
    parameters: List<Pair<String, String>>,
    preConditionClauses: Set<String>,
    variant: StoreVariant,
    mayBeUnset: Boolean,
  ): Set<SingleRefineryRule> =
    if (variant.retarget) {
      retargetRules(
        pointer = pointer,
        newTarget = target,
        parameters = parameters + variant.parameters,
        preConditionClauses = preConditionClauses + variant.preconditions,
        otherActions = variant.actions,
        mayBeUnset = mayBeUnset,
      )
    } else {
      setOf(
        SingleRefineryRule(
          parameters = parameters + variant.parameters,
          preConditionClauses = preConditionClauses + variant.preconditions,
          actionLiterals = variant.actions,
        )
      )
    }

  private var dereferenceCounter: Int = 0
  private var pointerArithmeticCounter: Int = 0
  private var pointerComparisonCounter: Int = 0

  protected sealed class RefineryRuleBlock {

    class Id(var id: Int) {

      override fun toString(): String = id.toString()
    }

    open lateinit var preId: Id
    open lateinit var postId: Id

    abstract val allRules: List<SingleRefineryRule>

    open fun setIds(preId: Id = Id(0), postId: Id = Id(-1)) {
      this.preId = preId
      this.postId = postId
    }
  }

  protected data class SingleRefineryRule(
    val parameters: List<Pair<String, String>> = listOf(),
    val preConditionClauses: Set<String> = setOf(),
    val actionLiterals: List<String> = listOf(),
    override var preId: Id = Id(-1),
    override var postId: Id = Id(-1),
  ) : RefineryRuleBlock() {

    override val allRules
      get() = listOf(this)

    override fun setIds(preId: Id, postId: Id) {
      if (postId.id <= preId.id) {
        postId.id = preId.id + 1
      }
      super.setIds(preId, postId)
    }

    fun toRefineryRule(transitionName: String): RefineryRule {
      val name = "${transitionName}__${preId}_to_${postId}"
      return RefineryRule(
        name = name,
        parameters = parameters,
        preConditionClauses = preConditionClauses,
        actionLiterals = actionLiterals,
      )
    }
  }

  protected class SequenceRefineryRuleBlock(val blocks: List<RefineryRuleBlock>) :
    RefineryRuleBlock() {

    init {
      check(blocks.isNotEmpty()) { "SequenceRefineryRuleBlock must contain at least one block." }
    }

    override val allRules
      get() = blocks.flatMap { it.allRules }

    override fun setIds(preId: Id, postId: Id) {
      super.setIds(preId, postId)
      for ((i, block) in blocks.withIndex()) {
        val pre = if (i == 0) preId else blocks[i - 1].postId
        val post = if (i == blocks.size - 1) postId else Id(-1)
        block.setIds(pre, post)
      }
    }
  }

  protected class NondetRefineryRuleBlock(val branches: Set<RefineryRuleBlock>) :
    RefineryRuleBlock() {

    init {
      check(branches.isNotEmpty()) { "NondetRefineryRuleBlock must contain at least one branch." }
    }

    override val allRules
      get() = branches.flatMap { it.allRules }

    override fun setIds(preId: Id, postId: Id) {
      super.setIds(preId, postId)
      branches.forEach { it.setIds(preId, postId) }
    }
  }

  /**
   * Represents an expression with preconditions, parameters and a final expression string. The
   * final expression is used when the expression is embedded in another expression. The type is
   * used to distinguish between pointer and non-pointer expressions.
   */
  protected data class RefineryExpr(
    val type: ExprType,
    val preConditionClauses: Set<String>,
    val expr: String,
    val parameters: Set<Pair<String, String>> = setOf(),
    /**
     * A node comparison, or a condition built from one: Refinery accepts it only as a precondition
     * literal, never inside a term or as a value.
     */
    val conditionOnly: Boolean = false,
  ) {

    enum class ExprType {
      POINTER,
      NON_POINTER,
    }

    companion object {

      fun single(
        type: ExprType,
        preConditionClauses: Set<String>,
        expr: String,
        parameters: Set<Pair<String, String>> = setOf(),
      ): Set<RefineryExpr> = setOf(RefineryExpr(type, preConditionClauses, expr, parameters))
    }
  }

  /**
   * Builds the rule(s) setting the target of [pointer] to [newTarget]. The reference is
   * single-valued and transition actions only overwrite the given tuple, so the old target must be
   * removed explicitly. If [mayBeUnset], a variant for a pointer without any target is added too.
   */
  private fun retargetRules(
    pointer: String,
    newTarget: String,
    parameters: List<Pair<String, String>>,
    preConditionClauses: Set<String>,
    otherActions: List<String> = listOf(),
    mayBeUnset: Boolean = false,
  ): Set<SingleRefineryRule> {
    val oldTarget = "old_target"
    val withOld =
      SingleRefineryRule(
        parameters = parameters + ("Pointable" to oldTarget),
        preConditionClauses = preConditionClauses + "target($pointer, $oldTarget)",
        actionLiterals =
          otherActions + listOf("!target($pointer, $oldTarget)", "target($pointer, $newTarget)"),
      )
    val withoutOld =
      SingleRefineryRule(
        parameters = parameters,
        preConditionClauses = preConditionClauses + "!target($pointer, _)",
        actionLiterals = otherActions + "target($pointer, $newTarget)",
      )
    return if (mayBeUnset) setOf(withOld, withoutOld) else setOf(withOld)
  }

  /** Return a set of refinery rules for the given transition. */
  abstract fun build(transition: T): Set<RefineryRule>

  protected fun Stmt.toRules(): RefineryRuleBlock {
    // Variable names are only unique within one statement's rule.
    clauseCache.clear()
    dereferenceCounter = 0
    pointerArithmeticCounter = 0
    pointerComparisonCounter = 0
    return when (this) {
      is AssignStmt<*> -> toRules()
      is AssumeStmt -> toRules()
      is MemoryAssignStmt<*, *, *> -> toRules()
      is SkipStmt -> SingleRefineryRule()
      is SequenceStmt ->
        SequenceRefineryRuleBlock(stmts.filter { it !is SkipStmt }.map { it.toRules() })

      else -> error("Unsupported statement in RefineryRuleBuilder: $this")
    }
  }

  private fun AssignStmt<*>.toRules(): RefineryRuleBlock {
    val name = varDecl.name.refinerified
    return if (varDecl in pointers) {
      val pointer = "pointer_$name"
      val commonPreconditions = mutableSetOf("pointer($name, $pointer)")
      if (expr is MemoryAllocationExpr<*>) {
        allocationRule(varDecl.ref, pointer, commonPreconditions, (expr as MemoryAllocationExpr<*>).size)
      } else {
        NondetRefineryRuleBlock(
          expr
            .getPointerExpr(this)
            .flatMap { (_, preconditions, pointerExpr, _) ->
              val target = "target"
              val preconditionsPointer = listOf("target($pointerExpr, $target)")
              storeVariants(varDecl.ref, expr, target).flatMap { variant ->
                storeRules(
                  pointer = pointer,
                  target = target,
                  parameters = listOf("Pointer" to pointer, "Pointable" to target),
                  preConditionClauses = commonPreconditions + preconditions + preconditionsPointer,
                  variant = variant,
                  mayBeUnset = false,
                )
              }
            }
            .toSet()
        )
      }
    } else {
      if (expr is MemoryDeallocationExpr<*>) {
        val expr = expr as MemoryDeallocationExpr<*>
        NondetRefineryRuleBlock(
          expr.getPointerExpr(this).map { (_, preconditions, pointerExpr, _) ->
            val target = "target"
            val region = "region"
            val preconditionsPointer = listOf("target($pointerExpr, $target)", "parts($region, $target)")

            SingleRefineryRule(
              parameters = listOf("MemoryRegion" to region),
              preConditionClauses = preconditions + preconditionsPointer,
              actionLiterals = listOf("!valid($region)"),
            )
          }.toSet()
        )
      } else {
        variables.add(varDecl)
        NondetRefineryRuleBlock(
          expr
            .getTermExpr(this)
            .map { (_, preconditions, expr, _) ->
              SingleRefineryRule(
                preConditionClauses = preconditions,
                actionLiterals = listOf("$name(): $expr"),
              )
            }
            .toSet()
        )
      }
    }
  }

  /**
   * Allocates a region of [size] bytes for [pointerExpr]. A typed pointer gets the region's parts at
   * once; an untyped one gets a single base part of yet unknown class.
   */
  private fun allocationRule(
    pointerExpr: Expr<*>,
    pointer: String,
    commonPreconditions: Set<String>,
    size: BigInteger?,
  ): RefineryRuleBlock {
    if (size == null) return SingleRefineryRule(actionLiterals = listOf(UNSUPPORTED_ACTION))
    val region = "allocated_region"
    val regionActions =
      listOf(
        "MemoryRegion::address($region): ${newRegionAddress(1)}",
        "MemoryRegion::size($region): $size",
        "valid($region)",
      )
    val parameters = listOf("Pointer" to pointer, "@new MemoryRegion" to region)
    val type = pointerTypeOf(pointerExpr)
    if (type !is RefineryPointerType.Typed) {
      val base = "allocated_base"
      return retargetRules(
          pointer = pointer,
          newTarget = base,
          parameters = parameters + ("@new MemoryObject" to base),
          preConditionClauses = commonPreconditions,
          otherActions =
            regionActions +
              listOf(
                "next_address(): ${newRegionAddress(1)}",
                "parts($region, $base)",
                "offset($base): 0",
              ),
        )
        .single()
    }
    val parts =
      regionParts(size, type.pointee)
        ?: return SingleRefineryRule(actionLiterals = listOf(UNSUPPORTED_ACTION))
    val interpreter = RegionInterpreter(1)
    val base = interpreter.interpret(region, type.pointee, parts, null)
    return retargetRules(
        pointer = pointer,
        newTarget = base,
        parameters = parameters + interpreter.parameters,
        preConditionClauses = commonPreconditions,
        otherActions = regionActions + interpreter.actions + interpreter.addressActions,
      )
      .single()
  }

  private fun AssumeStmt.toRules(): RefineryRuleBlock =
    NondetRefineryRuleBlock(
      cond
        .getNonPointerExpr(this)
        .map { (_, preconditions, expr, _) ->
          SingleRefineryRule(
            preConditionClauses = preconditions + listOf(expr),
          )
        }
        .toSet()
    )

  private fun MemoryAssignStmt<*, *, *>.toRules(): RefineryRuleBlock {
    val exprs = expr.toClauses()
    val derefs = deref.toClauses()
    val storedType = if (pointerTypeOf(deref) == RefineryPointerType.NotPointer) NON_POINTER else POINTER
    return NondetRefineryRuleBlock(
      exprs
        .flatMap { (exprType, exprPreconditions, exprExpr, exprParams) ->
          derefs.flatMap { (derefType, derefPreconditions, derefExpr, _) ->
            when {
              exprType != derefType || exprType != storedType -> setOf()

              exprType == POINTER -> {
                val target = "target"
                val preconditions =
                  exprPreconditions + derefPreconditions + "target($exprExpr, $target)"
                storeVariants(deref, expr, target).flatMap { variant ->
                  storeRules(
                    pointer = derefExpr,
                    target = target,
                    parameters = listOf("Pointer" to derefExpr, "Pointable" to target),
                    preConditionClauses = preconditions,
                    variant = variant,
                    // every pointer part gets a target when it is created
                    mayBeUnset = false,
                  )
                }
              }

              derefType == NON_POINTER -> {
                val derefStripped = derefExpr.removePrefix("value(").removeSuffix(")")
                val parameters = exprParams.toList()
                val derefStrippedVar = parameters.find { it.second == derefStripped }?.second ?: derefStripped
                val ruleParameters = (setOf("Value" to derefStrippedVar) + parameters).toList()

                setOf(
                  SingleRefineryRule(
                    parameters = ruleParameters,
                    preConditionClauses = exprPreconditions + derefPreconditions,
                    actionLiterals = listOf("value(${derefStrippedVar}): $exprExpr"),
                  )
                )
              }

              else -> error("Unreachable branch.")
            }
          }
        }
        .toSet()
    )
  }

  /**
   * Converts an expression to Refinery clauses.
   *
   * @return A set of possible prepared refinery expressions (see [RefineryExpr]).
   */
  private val clauseCache = IdentityHashMap<Expr<*>, Set<RefineryExpr>>()

  private fun Expr<*>.toClauses(): Set<RefineryExpr> =
    clauseCache[this] ?: computeClauses().also { clauseCache[this] = it }

  private fun Expr<*>.hasConditionOnly(): Boolean = toClauses().any { it.conditionOnly }

  /** A conjunction holding a condition-only operand: every operand is a precondition literal. */
  private fun conjunctionClauses(ops: List<Expr<*>>): Set<RefineryExpr> =
    ops
      .map { it.getNonPointerExpr(ops) }
      .combinations
      .map { conjuncts ->
        RefineryExpr(
          type = NON_POINTER,
          preConditionClauses =
            conjuncts.flatMap { it.preConditionClauses + it.expr }.toSet(),
          expr = "true",
          parameters = conjuncts.flatMap { it.parameters }.toSet(),
          conditionOnly = true,
        )
      }
      .toSet()

  private fun Expr<*>.computeClauses(): Set<RefineryExpr> =
    when (this) {
      is LitExpr<*> ->
        setOfNotNull(
          RefineryExpr(
            type = NON_POINTER,
            preConditionClauses = setOf(),
            expr =
              when (this) {
                is BoolLitExpr -> value.toString()
                is IntLitExpr -> value.toString()
                else -> error("Unsupported literal expression in RefineryRuleBuilder: $this")
              },
          ),
          when {
            this == Int(0) ->
              RefineryExpr(type = POINTER, preConditionClauses = setOf(), expr = "nullptr")
            this is IntLitExpr && value in staticObjects ->
              RefineryExpr(type = POINTER, preConditionClauses = setOf(), expr = staticPointer(value))
            else -> null
          },
        )

      is RefExpr<*> -> {
        val name = decl.name.refinerified
        if (decl in pointers) {
          val pointer = "pointer_$name"
          RefineryExpr.single(
            type = POINTER,
            preConditionClauses = setOf("pointer($name, $pointer)"),
            expr = pointer,
            parameters = setOf("Pointer" to pointer),
          )
        } else {
          variables.add(decl)
          RefineryExpr.single(
            type = NON_POINTER,
            preConditionClauses = setOf(),
            expr = "$name()",
          )
        }
      }

      is Dereference<*, *, *> -> {
        // Reading the other kind of part would be an error value that excludes the whole state.
        val readsPointer = pointerTypeOf(this) != RefineryPointerType.NotPointer
        val derefResult = { preconditions: Set<String>, referenced: String ->
          setOf(
            if (readsPointer) {
              RefineryExpr(
                type = POINTER,
                preConditionClauses = preconditions,
                expr = referenced,
                parameters = setOf("Pointer" to referenced),
              )
            } else {
              RefineryExpr(
                type = NON_POINTER,
                preConditionClauses = preconditions,
                expr = "value($referenced)",
                parameters = setOf("Value" to referenced),
              )
            }
          )
        }

        // An address that names no global object matches no region: the rule would silently drop
        // its paths.
        val arrayExprs =
          array.toClauses().filter { it.type == POINTER }.ifEmpty {
            throw UnsupportedOperationException(
              "Dereference of an unknown integer address is not supported by the Refinery encoding: $this"
            )
          }
        val derefCount = dereferenceCounter++
        arrayExprs.flatMap { (_, basePreconditions, baseExpr, _) ->
          val region = "region_${derefCount}"
          val base = "base_${derefCount}"
          val preconditions = basePreconditions.toMutableSet()
          preconditions.add("target($baseExpr, $base)")

          when {
            offset == Int(0) -> {
              derefResult(preconditions, base)
            }

            offset.type == Int() -> {
              val referenced = "referenced_${derefCount}"
              preconditions.add("parts($region, $base)")
              preconditions.add("parts($region, $referenced)")
              val offsetExprs = offset.getNonPointerExpr(this)
              offsetExprs.flatMap { (_, offsetPreconditions, offsetExpr, _) ->
                val preconditions = (preconditions + offsetPreconditions).toMutableSet()
                preconditions.add("offset($referenced) == offset($base) + ($offsetExpr)")
                derefResult(preconditions, referenced)
              }
            }

            else -> error("Unsupported offset expression in Dereference: ${this.offset}")
          }
        }
      }

      is AddExpr<*> -> {
        ops
          .map { it.toClauses() }
          .combinations
          .flatMap { ops ->
            val nonPointerExprWithParams =
              if (ops.any { it.type != NON_POINTER }) null
              else {
                RefineryExpr(
                  type = NON_POINTER,
                  preConditionClauses = ops.flatMap { it.preConditionClauses }.toSet(),
                  expr = ops.map { it.expr }.join("+"),
                  parameters = ops.flatMap { it.parameters }.toSet(),
                )
              }

            val pointerArithmeticSupported = ops.count { it.type == POINTER } == 1
            val pointerExprWithParams =
              if (pointerArithmeticSupported) {
                val pointerOp = ops.first { it.type == POINTER }
                val pointerPreconditions = pointerOp.preConditionClauses
                val pointer = pointerOp.expr
                val pointerParams = pointerOp.parameters
                val nonPointerOps = ops.filter { it.type != POINTER }
                val nonPointerPreconditions = nonPointerOps.flatMap { it.preConditionClauses }
                val nonPointerSum = nonPointerOps.map { it.expr }.join("+")
                val nonPointerParams = nonPointerOps.flatMap { it.parameters }.toSet()
                val pointerArithmeticCount = pointerArithmeticCounter++

                val preconditions = (pointerPreconditions + nonPointerPreconditions).toMutableSet()
                val base = "ptr_arith_base_${pointerArithmeticCount}"
                val region = "ptr_arith_region_${pointerArithmeticCount}"
                val referenced = "ptr_arith_referenced_${pointerArithmeticCount}"
                preconditions.add("target($pointer, $base)")
                preconditions.add("parts($region, $base)")
                preconditions.add("parts($region, $referenced)")
                preconditions.add("offset($referenced) == offset($base) + ($nonPointerSum)")
                RefineryExpr(
                  type = POINTER,
                  preConditionClauses = preconditions,
                  expr = referenced,
                  parameters = pointerParams + nonPointerParams,
                )
              } else null

            setOfNotNull(pointerExprWithParams, nonPointerExprWithParams)
          }
      }

      is ModExpr<*> -> {
        val lExprs = leftOp.toClauses()
        val rExprs = rightOp.toClauses()
        lExprs.flatMap { (lType, lPreconditions, lExpr, lParams) ->
          rExprs.mapNotNull { (rType, rPreconditions, rExpr, rParams) ->
            when (lType) {
              NON_POINTER if rType == NON_POINTER -> {
                RefineryExpr(
                  type = NON_POINTER,
                  preConditionClauses = lPreconditions + rPreconditions,
                  // No mod operator in Refinery
                  expr = "($lExpr) - ((($lExpr) / ($rExpr)) * ($rExpr))",
                  parameters = lParams + rParams,
                )
              }

              POINTER if rType == NON_POINTER -> {
                // skipping mod for pointers
                RefineryExpr(lType, lPreconditions, lExpr, lParams)
              }

              else -> null
            }
          }
        }
      }

      is EqExpr<*> -> equalityCheck("==")
      is NeqExpr<*> -> equalityCheck("!=")

      is AndExpr ->
        if (ops.any { it.hasConditionOnly() }) conjunctionClauses(ops)
        else toNonPointerClauses("&&")
      is OrExpr ->
        // Each disjunct becomes a rule of its own.
        if (ops.any { it.hasConditionOnly() }) {
          ops.flatMap { op -> op.getNonPointerExpr(this).map { it.copy(conditionOnly = true) } }
        } else toNonPointerClauses("||")
      is NotExpr ->
        when (val op = op) {
          is EqExpr<*> -> NeqExpr.create2(op.leftOp, op.rightOp).toClauses()
          is NeqExpr<*> -> EqExpr.create2(op.leftOp, op.rightOp).toClauses()
          is NotExpr -> op.op.toClauses()
          is AndExpr if op.hasConditionOnly() -> Or(op.ops.map { Not(it) }).toClauses()
          is OrExpr if op.hasConditionOnly() -> And(op.ops.map { Not(it) }).toClauses()
          else -> toNonPointerClauses("!")
        }

      is PosExpr<*> -> op.toClauses()

      is UnaryExpr<*, *> -> toNonPointerClauses()
      is BinaryExpr<*, *> -> toNonPointerClauses()
      is MultiaryExpr<*, *> -> toNonPointerClauses()

      is IteExpr<*> -> {
        val getBranchExprs = { condExprs: Set<RefineryExpr>, branchExprs: Set<RefineryExpr> ->
          condExprs.flatMap { (_, condPreconditions, condExpr, _) ->
            branchExprs.map {
              it.copy(preConditionClauses = condPreconditions + listOf(condExpr) + it.preConditionClauses)
            }
          }
        }

        val condExprs = cond.getNonPointerExpr(this)
        val thenExprs = then.toClauses()
        val positiveExprs = getBranchExprs(condExprs, thenExprs)

        val notCondExprs = Not(cond).getNonPointerExpr(this)
        val elseExprs = `else`.toClauses()
        val negativeExprs = getBranchExprs(notCondExprs, elseExprs)

        positiveExprs + negativeExprs
      }

      else -> error("Unsupported expression in RefineryRuleBuilder: $this")
    }.let { result: Collection<RefineryExpr> ->
      check(result.isNotEmpty()) { "At least one expression expected at $this, but got none." }
      result.toSet()
    }

  private fun List<String>.join(operator: String): String =
    this.joinToString(" $operator ") { "($it)" }

  private fun Expr<*>.getPointerExpr(parent: Any): Set<RefineryExpr> =
    this.toClauses()
      .filter { it.type == POINTER }
      .let {
        check(it.isNotEmpty()) {
          "Pointer expression expected at $parent, expression $this does not yield a pointer expression."
        }
        it.toSet()
      }

  private fun Expr<*>.getNonPointerExpr(parent: Any): Set<RefineryExpr> =
    this.toClauses()
      .filter { it.type == NON_POINTER }
      .let {
        check(it.isNotEmpty()) {
          "Non-pointer expression expected at $parent, expression $this does not yield a non-pointer expression."
        }
        it.toSet()
      }

  /** A value to embed in a term: a condition-only expression cannot be one. */
  private fun Expr<*>.getTermExpr(parent: Any): Set<RefineryExpr> =
    getNonPointerExpr(parent).also { exprs ->
      if (exprs.any { it.conditionOnly }) {
        throw UnsupportedOperationException(
          "A pointer comparison used as a value is not supported by the Refinery encoding: $parent"
        )
      }
    }

  private fun BinaryExpr<*, *>.equalityCheck(operator: String): Collection<RefineryExpr> {
    val lExprs = leftOp.toClauses()
    val rExprs = rightOp.toClauses()

    return lExprs.flatMap { (lType, lPreconditions, lExpr, lParams) ->
      rExprs.mapNotNull { (rType, rPreconditions, rExpr, rParams) ->
        when {
          lType != rType -> null
          lType == NON_POINTER -> {
            RefineryExpr(
              type = NON_POINTER,
              preConditionClauses = lPreconditions + rPreconditions,
              expr = "$lExpr $operator $rExpr",
              parameters = lParams + rParams,
            )
          }

          lType == POINTER -> {
            val preconditions = (lPreconditions + rPreconditions).toMutableSet()
            val pointerComparisonCount = pointerComparisonCounter++
            val lTarget = "pointer_comp_target_left_${pointerComparisonCount}"
            val rTarget = "pointer_comp_target_right_${pointerComparisonCount}"
            preconditions.add("target(${lExpr}, $lTarget)")
            preconditions.add("target(${rExpr}, $rTarget)")
            RefineryExpr(
              type = NON_POINTER,
              preConditionClauses = preconditions,
              expr = "$lTarget $operator $rTarget",
              parameters = lParams + rParams,
              conditionOnly = true,
            )
          }

          else -> error("Unreachable branch.")
        }
      }
    }
  }

  private fun UnaryExpr<*, *>.toNonPointerClauses(
    operator: String = operatorLabel
  ): Collection<RefineryExpr> {
    check(operator in supportedOperators) {
      "Unsupported operator '$operator' at $this in RefineryRuleBuilder."
    }
    val innerExprs = op.getTermExpr(this)
    return innerExprs.map { (_, innerPreconditions, innerExpr, innerParams) ->
      RefineryExpr(
        type = NON_POINTER,
        preConditionClauses = innerPreconditions,
        expr = "$operator($innerExpr)",
        parameters = innerParams,
      )
    }
  }

  private fun BinaryExpr<*, *>.toNonPointerClauses(
    operator: String = operatorLabel
  ): Collection<RefineryExpr> {
    check(operator in supportedOperators) {
      "Unsupported operator '$operator' at $this in RefineryRuleBuilder."
    }
    val lExprs = leftOp.getTermExpr(this)
    val rExprs = rightOp.getTermExpr(this)
    return lExprs.flatMap { (_, lPreconditions, lExpr, lParams) ->
      rExprs.map { (_, rPreconditions, rExpr, rParams) ->
        RefineryExpr(
          type = NON_POINTER,
          preConditionClauses = lPreconditions + rPreconditions,
          expr = "($lExpr) $operator ($rExpr)",
          parameters = lParams + rParams,
        )
      }
    }
  }

  private fun MultiaryExpr<*, *>.toNonPointerClauses(
    operator: String = operatorLabel
  ): Collection<RefineryExpr> {
    check(operator in supportedOperators) {
      "Unsupported operator '$operator' at $this in RefineryRuleBuilder."
    }
    return ops
      .map { it.getTermExpr(this) }
      .combinations
      .map { ops ->
        RefineryExpr(
          type = NON_POINTER,
          preConditionClauses = ops.flatMap { it.preConditionClauses }.toSet(),
          expr = ops.map { it.expr }.join(operator),
          parameters = ops.flatMap { it.parameters }.toSet(),
        )
      }
  }

  private inline val <T> List<Set<T>>.combinations: Set<List<T>>
    get() =
      fold(listOf(listOf<T>())) { acc, set -> acc.flatMap { prefix -> set.map { prefix + it } } }
        .toSet()
}
