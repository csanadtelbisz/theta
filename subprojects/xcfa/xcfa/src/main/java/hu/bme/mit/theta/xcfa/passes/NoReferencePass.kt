/*
 *  Copyright 2024-2025 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.anytype.Reference
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.model.*

/** Removes unused locations */
class NoReferencePass : ProcedurePass {

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    if (builder.getEdges().flatMap { it.getFlatLabels() }.any { getReferences(it).isNotEmpty() }) {
      error("Reference not supported")
    }
    return builder
  }

  private fun getReferences(label: XcfaLabel): List<Reference<*, *>> =
    when (label) {
      is StmtLabel ->
        when (label.stmt) {
          is AssumeStmt -> getReferences(label.stmt.cond)
          is AssignStmt<*> -> getReferences(label.stmt.expr)
          else -> emptyList()
        }

      is InvokeLabel -> label.params.flatMap { getReferences(it) }
      is NondetLabel -> label.labels.flatMap { getReferences(it) }
      is SequenceLabel -> label.labels.flatMap { getReferences(it) }
      is StartLabel -> label.params.flatMap { getReferences(it) }
      else -> emptyList()
    }

  private fun getReferences(expr: Expr<*>): List<Reference<*, *>> =
    if (expr is Reference<*, *>) {
      listOf(expr)
    } else {
      expr.ops.flatMap { getReferences(it) }
    }
}
