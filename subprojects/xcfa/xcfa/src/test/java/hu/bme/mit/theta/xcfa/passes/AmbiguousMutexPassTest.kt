/*
 *  Copyright 2026 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.xcfa.model.XcfaBuilder
import hu.bme.mit.theta.xcfa.model.procedure
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertNotSame
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

class AmbiguousMutexPassTest {

  @Test
  fun parallelEdgesKeepSeparateSplitLocations() {
    val builder =
      XcfaBuilder("")
        .procedure("main") {
          "m" type Int()
          "x" type Int()
          (init to final) {
            "x".assign("1")
            mutex_unlock("m")
            skip()
          }
          (init to final) {
            "x".assign("2")
            mutex_unlock("m")
            skip()
          }
        }
        .builder

    val result =
      listOf(NormalizePass(), DeterministicPass(), AmbiguousMutexPass()).fold(builder) { acc, pass
        ->
        pass.runChecked(acc)
      }

    val branches = result.initLoc.outgoingEdges.toList()
    assertEquals(2, branches.size)
    assertNotSame(branches[0].target, branches[1].target)
    assertEquals(2, branches.map { it.target.name }.toSet().size)
    result.getEdges().forEach { edge ->
      assertTrue(result.getLocs().any { it === edge.source })
      assertTrue(result.getLocs().any { it === edge.target })
    }
    branches.forEach { branch ->
      val unlock = branch.target.outgoingEdges.single()
      assertTrue(unlock.target === result.finalLoc.get())
    }
  }
}
