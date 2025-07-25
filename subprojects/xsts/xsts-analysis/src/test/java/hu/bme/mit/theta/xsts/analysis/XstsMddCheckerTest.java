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
package hu.bme.mit.theta.xsts.analysis;

import static org.junit.Assert.assertTrue;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.mdd.MddChecker;
import hu.bme.mit.theta.analysis.algorithm.mdd.MddChecker.IterationStrategy;
import hu.bme.mit.theta.analysis.algorithm.mdd.MddProof;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.solver.SolverPool;
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory;
import hu.bme.mit.theta.xsts.XSTS;
import hu.bme.mit.theta.xsts.analysis.hu.bme.mit.theta.xsts.analysis.XstsToMonolithicExprKt;
import hu.bme.mit.theta.xsts.dsl.XstsDslManager;
import java.io.FileInputStream;
import java.io.InputStream;
import java.io.SequenceInputStream;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

public class XstsMddCheckerTest {

    public static Collection<Object[]> data() {
        return Arrays.asList(
                new Object[][] {
                    //                                        {
                    //
                    // "src/test/resources/model/spacecraft.xsts",
                    //
                    //
                    // "src/test/resources/property/transmitting_battery_40.prop",
                    //                                            false
                    //                                        },

                    //                { "src/test/resources/model/trafficlight.xsts",
                    // "src/test/resources/property/green_and_red.prop", true},

                    {
                        "src/test/resources/model/trafficlight_v2.xsts",
                        "src/test/resources/property/green_and_red.prop",
                        true
                    },
                    {
                        "src/test/resources/model/counter5.xsts",
                        "src/test/resources/property/x_between_0_and_5.prop",
                        true
                    },
                    {
                        "src/test/resources/model/counter5.xsts",
                        "src/test/resources/property/x_eq_5.prop",
                        false
                    },
                    {
                        "src/test/resources/model/x_and_y.xsts",
                        "src/test/resources/property/x_geq_y.prop",
                        true
                    },
                    {
                        "src/test/resources/model/x_powers.xsts",
                        "src/test/resources/property/x_even.prop",
                        true
                    },

                    //                                    {
                    // "src/test/resources/model/cross_with.xsts",
                    //                     "src/test/resources/property/cross.prop", false},
                    //
                    //                                    {
                    // "src/test/resources/model/cross_without.xsts",
                    //                     "src/test/resources/property/cross.prop", false},

                    {
                        "src/test/resources/model/choices.xsts",
                        "src/test/resources/property/choices.prop",
                        false
                    },

                    //                { "src/test/resources/model/literals.xsts",
                    // "src/test/resources/property/literals.prop", true},

                    //                { "src/test/resources/model/cross3.xsts",
                    // "src/test/resources/property/cross.prop", false},

                    {
                        "src/test/resources/model/sequential.xsts",
                        "src/test/resources/property/sequential.prop",
                        true
                    },
                    {
                        "src/test/resources/model/sequential.xsts",
                        "src/test/resources/property/sequential2.prop",
                        false
                    },
                    //                                        {
                    //
                    // "src/test/resources/model/on_off_statemachine.xsts",
                    //
                    //                     "src/test/resources/property/on_off_statemachine.prop",
                    //                                            false
                    //                                        },
                    //                                        {
                    //
                    // "src/test/resources/model/on_off_statemachine.xsts",
                    //
                    //                     "src/test/resources/property/on_off_statemachine2.prop",
                    //                                            true
                    //                                        },
                    //                    {
                    //                        "src/test/resources/model/on_off_statemachine.xsts",
                    //
                    // "src/test/resources/property/on_off_statemachine3.prop",
                    //                        false
                    //                    },

                    {
                        "src/test/resources/model/counter50.xsts",
                        "src/test/resources/property/x_eq_5.prop",
                        false
                    },
                    {
                        "src/test/resources/model/counter50.xsts",
                        "src/test/resources/property/x_eq_50.prop",
                        false
                    },
                    {
                        "src/test/resources/model/counter50.xsts",
                        "src/test/resources/property/x_eq_51.prop",
                        true
                    },
                    {
                        "src/test/resources/model/count_up_down.xsts",
                        "src/test/resources/property/count_up_down.prop",
                        false
                    },
                    {
                        "src/test/resources/model/count_up_down.xsts",
                        "src/test/resources/property/count_up_down2.prop",
                        true
                    },
                    {
                        "src/test/resources/model/count_up_down.xsts",
                        "src/test/resources/property/count_up_down2.prop",
                        true
                    },
                    {
                        "src/test/resources/model/bhmr2007.xsts",
                        "src/test/resources/property/bhmr2007.prop",
                        true
                    },
                    //                    {
                    //                        "src/test/resources/model/css2003.xsts",
                    //                        "src/test/resources/property/css2003.prop",
                    //                        true
                    //                    },
                    //
                    //                { "src/test/resources/model/array_counter.xsts",
                    // "src/test/resources/property/array_10.prop", false},
                    //
                    //                { "src/test/resources/model/array_constant.xsts",
                    // "src/test/resources/property/array_constant.prop", true},
                    //
                    //                { "src/test/resources/model/localvars.xsts",
                    // "src/test/resources/property/localvars.prop", true},
                    //
                    //                { "src/test/resources/model/localvars2.xsts",
                    // "src/test/resources/property/localvars2.prop", true},
                    //
                    //                { "src/test/resources/model/loopxy.xsts",
                    // "src/test/resources/property/loopxy.prop", true},
                    //
                    //                { "src/test/resources/model/arraywrite_sugar.xsts",
                    // "src/test/resources/property/arraywrite_sugar.prop", false},
                    //
                    //                { "src/test/resources/model/if1.xsts",
                    // "src/test/resources/property/if1.prop", true},
                    //
                    //                { "src/test/resources/model/if2.xsts",
                    // "src/test/resources/property/if2.prop", false}

                    {
                        "src/test/resources/model/localvars3.xsts",
                        "src/test/resources/property/localvars3.prop",
                        false
                    },
                });
    }

    public static void runTestWithIterationStrategy(
            String filePath, String propPath, boolean safe, IterationStrategy iterationStrategy)
            throws Exception {
        final Logger logger = new ConsoleLogger(Logger.Level.SUBSTEP);

        XSTS xsts;
        try (InputStream inputStream =
                new SequenceInputStream(
                        new FileInputStream(filePath), new FileInputStream(propPath))) {
            xsts = XstsDslManager.createXsts(inputStream);
        }

        final SafetyResult<MddProof, Trace<ExprState, ExprAction>> status;
        try (var solverPool = new SolverPool(Z3LegacySolverFactory.getInstance())) {
            var monolithicExpr = XstsToMonolithicExprKt.toMonolithicExpr(xsts);
            var checker =
                    MddChecker.create(
                            monolithicExpr,
                            List.copyOf(monolithicExpr.getVars()),
                            solverPool,
                            logger,
                            MddChecker.IterationStrategy.GSAT,
                            valuation -> monolithicExpr.getValToState().invoke(valuation),
                            (Valuation v1, Valuation v2) ->
                                    monolithicExpr.getBiValToAction().invoke(v1, v2),
                            true);
            status = checker.check(null);
            logger.mainStep(status.toString());
        }

        if (safe) {
            assertTrue(status.isSafe());
        } else {
            assertTrue(status.isUnsafe());
            assertTrue(status.asUnsafe().getCex().length() > 0);
        }
    }
}
