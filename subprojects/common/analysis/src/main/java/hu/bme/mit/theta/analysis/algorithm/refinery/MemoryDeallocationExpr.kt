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
package hu.bme.mit.theta.analysis.algorithm.refinery

import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.UnaryExpr
import java.util.*

class MemoryDeallocationExpr<T : Type>(
  val pointer: Expr<T>,
) : UnaryExpr<T, T>(pointer) {

  companion object {

    const val OPERATOR_LABEL: String = "free"
    const val HASH_SEED: Int = 914
  }

  override fun getType(): T = pointer.type

  override fun eval(`val`: Valuation): LitExpr<T> = error("$this is not meant to be evaluated.")

  override fun hashCode(): Int = Objects.hash(pointer)

  override fun equals(other: Any?): Boolean {
    if (other is MemoryDeallocationExpr<*>) {
      return this.pointer == other.pointer
    }
    return false
  }

  override fun with(op: Expr<T>): UnaryExpr<T, T> =
    if (op == pointer) this
    else MemoryDeallocationExpr(op)

  override fun getHashSeed(): Int = HASH_SEED

  override fun getOperatorLabel(): String = OPERATOR_LABEL
}
