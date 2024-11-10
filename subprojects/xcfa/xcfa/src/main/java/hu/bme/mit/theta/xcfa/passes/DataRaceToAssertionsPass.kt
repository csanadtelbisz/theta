/*
 *  Copyright 2024 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.xcfa.*
import hu.bme.mit.theta.xcfa.model.*
import java.util.Stack

class DataRaceToAssertionsPass : ProcedurePass {

  companion object {
    private val varToWriteFlag = mutableMapOf<VarDecl<*>, VarDecl<BoolType>>()

    private val racingVars = mutableMapOf<XcfaBuilder, Set<VarDecl<*>>>()
    private val initEdges = mutableMapOf<XcfaBuilder, Set<Pair<XcfaLocation, XcfaLocation>>>()
  }

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    val racingGlobalVars = builder.parent.racingVars
    val edges = builder.getEdges() - builder.parent.initEdges
    edges.forEach { e ->
      val splitEdges = e.splitIf { it.isAtomicBegin || it.isAtomicEnd }
      if (splitEdges.isNotEmpty()) {
        builder.removeEdge(e)
      }
      splitEdges.forEach { edge ->
        val edgeGlobalVars = edge.collectGlobalVars(racingGlobalVars)
        if (edgeGlobalVars.isNotEmpty()) {
          val writeFlags = mutableMapOf<VarDecl<BoolType>, Boolean>()
          edgeGlobalVars.forEach { (v, access) ->
            val flag =
              varToWriteFlag.getOrPut(v) {
                val flagName = "${v.name}__writeflag${varToWriteFlag.size}"
                val flagVar = Decls.Var(flagName, Bool())
                builder.parent.addVar(XcfaGlobalVar(flagVar, False()))
                val initLabel = AssignStmtLabel(flagVar, False())
                builder.parent.getInitProcedures().forEach { (proc, _) ->
                  val newInitEdges =
                    proc.initLoc.outgoingEdges.map {
                      it.withLabel(
                        SequenceLabel(listOf(initLabel) + it.getFlatLabels(), it.label.metadata)
                      )
                    }
                  proc.initLoc.outgoingEdges.forEach(proc::removeEdge)
                  newInitEdges.forEach(proc::addEdge)
                }
                flagVar
              }
            writeFlags[flag] = writeFlags.getOrDefault(flag, false) || access.isWritten
          }

          val assertion = And(writeFlags.map { (flag, _) -> Not(flag.ref) })
          val positiveLabel =
            SequenceLabel(
              listOf(StmtLabel(AssumeStmt.of(assertion))) +
                writeFlags.mapNotNull { if (it.value) AssignStmtLabel(it.key, True()) else null }
            )
          val negativeLabel = StmtLabel(AssumeStmt.of(Not(assertion)))

          val intermediateLoc =
            XcfaLocation("${edge.source.name}_writeflagcheck", metadata = EmptyMetaData)
          builder.addLoc(intermediateLoc)
          if (builder.errorLoc.isEmpty) builder.createErrorLoc()

          val positiveEdge = XcfaEdge(edge.source, intermediateLoc, positiveLabel, edge.metadata)
          val originalEdge =
            XcfaEdge(
              intermediateLoc,
              edge.target,
              SequenceLabel(
                listOf(edge.label) +
                  writeFlags.mapNotNull { if (it.value) AssignStmtLabel(it.key, False()) else null }
              ),
              edge.metadata,
            )
          val negativeEdge =
            XcfaEdge(edge.source, builder.errorLoc.get(), negativeLabel, edge.metadata)

          builder.addEdge(positiveEdge)
          builder.addEdge(originalEdge)
          builder.addEdge(negativeEdge)
        } else {
          builder.addEdge(edge)
        }
      }
    }
    return builder
  }

  private val XcfaBuilder.racingVars: Set<VarDecl<*>>
    get() =
      Companion.racingVars.getOrPut(this) {
        getVars() // TODO filter out atomic variables
          .map { it.wrappedVar }
          .filter { v ->
            getProcedures().count { proc ->
              (proc.getEdges() - initEdges).any { edge ->
                edge.collectGlobalVars(setOf(v)).isNotEmpty()
              }
            } > 1
          }
          .toSet()
      }

  private val XcfaBuilder.initEdges: Set<Pair<XcfaLocation, XcfaLocation>>
    get() =
      Companion.initEdges.getOrPut(this) {
        val initProc = getInitProcedures().first().first
        val startEdges =
          initProc.getEdges().filter { e -> e.getFlatLabels().any { it is StartLabel } }
        val goodEdges = mutableSetOf<XcfaEdge>() // race cannot happen on these
        val badEdges = mutableSetOf<XcfaEdge>()
        startEdges
          .flatMap { it.source.incomingEdges }
          .forEach { e ->
            val stack = Stack<XcfaEdge>()
            stack.push(e)
            while (stack.isNotEmpty()) {
              val edge = stack.peek()
              if (edge.getFlatLabels().any { it is StartLabel }) {
                badEdges.addAll(stack)
              } else if (edge.source == initProc.initLoc) {
                goodEdges.add(edge)
              }
              edge.source.incomingEdges
                .firstOrNull { it !in goodEdges && it !in badEdges }
                ?.let { stack.push(it) }
                ?: run {
                  if (edge !in badEdges) {
                    goodEdges.add(edge)
                  }
                  stack.pop()
                }
            }
          }
        goodEdges.map { it.source to it.target }.toSet()
      }

  private operator fun Collection<XcfaEdge>.minus(
    edges: Collection<Pair<XcfaLocation, XcfaLocation>>
  ): Collection<XcfaEdge> = filter { e ->
    edges.none { e.source == it.first && e.target == it.second }
  }
}
