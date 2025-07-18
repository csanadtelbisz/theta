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
package hu.bme.mit.theta.analysis.algorithm.mdd;

import static com.google.common.base.Preconditions.checkArgument;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not;

import com.google.common.collect.Lists;
import hu.bme.mit.delta.java.mdd.JavaMddFactory;
import hu.bme.mit.delta.java.mdd.MddGraph;
import hu.bme.mit.delta.java.mdd.MddHandle;
import hu.bme.mit.delta.java.mdd.MddVariableOrder;
import hu.bme.mit.delta.mdd.MddInterpreter;
import hu.bme.mit.delta.mdd.MddVariableDescriptor;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr;
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExprKt;
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExprVarOrderingKt;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.AbstractNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.*;
import hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode.ExprLatticeDefinition;
import hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode.MddExplicitRepresentationExtractor;
import hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode.MddExpressionTemplate;
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.*;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.Logger.Level;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.solver.SolverPool;
import java.util.ArrayList;
import java.util.List;
import java.util.function.BiFunction;
import java.util.function.Function;

public class MddChecker<S extends ExprState, A extends ExprAction>
        implements SafetyChecker<MddProof, Trace<S, A>, UnitPrec> {

    private final MonolithicExpr monolithicExpr;
    private final List<VarDecl<?>> variableOrdering;
    private final SolverPool solverPool;
    private final Logger logger;
    private final IterationStrategy iterationStrategy;
    private final Function<Valuation, S> valToState;
    private final BiFunction<Valuation, Valuation, A> biValToAction;
    private final boolean forwardTrace;

    public enum IterationStrategy {
        BFS,
        SAT,
        GSAT
    }

    private MddChecker(
            MonolithicExpr monolithicExpr,
            List<VarDecl<?>> variableOrdering,
            SolverPool solverPool,
            Logger logger,
            IterationStrategy iterationStrategy,
            Function<Valuation, S> valToState,
            BiFunction<Valuation, Valuation, A> biValToAction,
            boolean forwardTrace) {
        this.monolithicExpr = monolithicExpr;
        this.variableOrdering = variableOrdering;
        this.solverPool = solverPool;
        this.logger = logger;
        this.iterationStrategy = iterationStrategy;
        this.valToState = valToState;
        this.biValToAction = biValToAction;
        this.forwardTrace = forwardTrace;
    }

    public static <S extends ExprState, A extends ExprAction> MddChecker<S, A> create(
            MonolithicExpr monolithicExpr,
            List<VarDecl<?>> variableOrdering,
            SolverPool solverPool,
            Logger logger,
            Function<Valuation, S> valToState,
            BiFunction<Valuation, Valuation, A> biValToAction,
            boolean forwardTrace) {
        return new MddChecker<S, A>(
                monolithicExpr,
                variableOrdering,
                solverPool,
                logger,
                IterationStrategy.GSAT,
                valToState,
                biValToAction,
                forwardTrace);
    }

    public static <S extends ExprState, A extends ExprAction> MddChecker<S, A> create(
            MonolithicExpr monolithicExpr,
            List<VarDecl<?>> variableOrdering,
            SolverPool solverPool,
            Logger logger,
            IterationStrategy iterationStrategy,
            Function<Valuation, S> valToState,
            BiFunction<Valuation, Valuation, A> biValToAction,
            boolean forwardTrace) {
        return new MddChecker<S, A>(
                monolithicExpr,
                variableOrdering,
                solverPool,
                logger,
                iterationStrategy,
                valToState,
                biValToAction,
                forwardTrace);
    }

    @Override
    public SafetyResult<MddProof, Trace<S, A>> check(UnitPrec prec) {

        final MddGraph<Expr> mddGraph =
                JavaMddFactory.getDefault().createMddGraph(ExprLatticeDefinition.forExpr());

        final MddVariableOrder stateOrder =
                JavaMddFactory.getDefault().createMddVariableOrder(mddGraph);
        final MddVariableOrder transOrder =
                JavaMddFactory.getDefault().createMddVariableOrder(mddGraph);

        variableOrdering.forEach(
                v ->
                        checkArgument(
                                monolithicExpr.getVars().contains(v),
                                "Variable ordering contains variable not present in vars List"));

        checkArgument(
                variableOrdering.size() == Containers.createSet(variableOrdering).size(),
                "Variable ordering contains duplicates");
        final var identityExprs = new ArrayList<Expr<BoolType>>();
        final var orderedVars = MonolithicExprVarOrderingKt.orderVars(monolithicExpr);
        for (var v : Lists.reverse(orderedVars)) {
            var domainSize = Math.max(v.getType().getDomainSize().getFiniteSize().intValue(), 0);

            //     if (domainSize > 100) {
            domainSize = 0;
            //     }

            stateOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(0), domainSize));

            final var index = monolithicExpr.getTransOffsetIndex().get(v);
            if (index > 0) {
                transOrder.createOnTop(
                        MddVariableDescriptor.create(
                                v.getConstDecl(monolithicExpr.getTransOffsetIndex().get(v)),
                                domainSize));
            } else {
                transOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(1), domainSize));
                identityExprs.add(Eq(v.getConstDecl(0).getRef(), v.getConstDecl(1).getRef()));
            }

            transOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(0), domainSize));
        }

        final var stateSig = stateOrder.getDefaultSetSignature();
        final var transSig = transOrder.getDefaultSetSignature();

        final Expr<BoolType> initExpr = PathUtils.unfold(monolithicExpr.getInitExpr(), 0);
        final MddHandle initNode =
                stateSig.getTopVariableHandle()
                        .checkInNode(MddExpressionTemplate.of(initExpr, o -> (Decl) o, solverPool));

        logger.write(Level.INFO, "Created initial node\n");

        final var transNodes = new ArrayList<MddHandle>();
        final List<AbstractNextStateDescriptor> descriptors = new ArrayList<>();
        for (var expr : MonolithicExprKt.split(monolithicExpr)) {
            final Expr<BoolType> transExpr =
                    And(PathUtils.unfold(expr, VarIndexingFactory.indexing(0)), And(identityExprs));
            final MddHandle transitionNode =
                    transSig.getTopVariableHandle()
                            .checkInNode(
                                    MddExpressionTemplate.of(
                                            transExpr, o -> (Decl) o, solverPool, true));
            transNodes.add(transitionNode);
            descriptors.add(MddNodeNextStateDescriptor.of(transitionNode));
        }
        final AbstractNextStateDescriptor nextStates = OrNextStateDescriptor.create(descriptors);

        final Expr<BoolType> negatedPropExpr =
                PathUtils.unfold(Not(monolithicExpr.getPropExpr()), 0);
        final MddHandle propNode =
                stateSig.getTopVariableHandle()
                        .checkInNode(
                                MddExpressionTemplate.of(
                                        negatedPropExpr, o -> (Decl) o, solverPool));
        final AbstractNextStateDescriptor targetedNextStates =
                OnTheFlyReachabilityNextStateDescriptor.of(nextStates, propNode);

        logger.write(Level.INFO, "Created next-state node, starting fixed point calculation");

        final StateSpaceEnumerationProvider stateSpaceProvider;
        switch (iterationStrategy) {
            case BFS -> {
                stateSpaceProvider = new BfsProvider(stateSig.getVariableOrder());
            }
            case SAT -> {
                stateSpaceProvider = new SimpleSaturationProvider(stateSig.getVariableOrder());
            }
            case GSAT -> {
                stateSpaceProvider = new GeneralizedSaturationProvider(stateSig.getVariableOrder());
            }
            default -> throw new IllegalStateException("Unexpected value: " + iterationStrategy);
        }
        final MddHandle stateSpace =
                stateSpaceProvider.compute(
                        MddNodeInitializer.of(initNode),
                        targetedNextStates,
                        stateSig.getTopVariableHandle());

        logger.write(Level.INFO, "Enumerated state-space");

        final MddHandle propViolating = (MddHandle) stateSpace.intersection(propNode);

        logger.write(Level.INFO, "Calculated violating states");

        final Long violatingSize = MddInterpreter.calculateNonzeroCount(propViolating);
        logger.write(Level.INFO, "States violating the property: " + violatingSize);

        final Long stateSpaceSize = MddInterpreter.calculateNonzeroCount(stateSpace);
        logger.write(Level.DETAIL, "State space size: " + stateSpaceSize);

        final MddAnalysisStatistics statistics =
                new MddAnalysisStatistics(
                        violatingSize,
                        stateSpaceSize,
                        stateSpaceProvider.getHitCount(),
                        stateSpaceProvider.getQueryCount(),
                        stateSpaceProvider.getCacheSize());

        logger.write(Level.MAINSTEP, "%s\n", statistics);

        // var explTrans = MddExplicitRepresentationExtractor.INSTANCE.transform(transitionNode,
        // transSig.getTopVariableHandle());

        final SafetyResult<MddProof, Trace<S, A>> result;
        if (violatingSize != 0) {
            var reversedDescriptors = new ArrayList<AbstractNextStateDescriptor>();
            for (var transNode : transNodes) {
                final var explTrans =
                        MddExplicitRepresentationExtractor.INSTANCE.transform(
                                transNode, transSig.getTopVariableHandle());
                reversedDescriptors.add(ReverseNextStateDescriptor.of(stateSpace, explTrans));
            }
            final var orReversed = OrNextStateDescriptor.create(reversedDescriptors);

            final TraceProvider traceProvider = new TraceProvider(stateSig.getVariableOrder());
            final var mddTrace =
                    traceProvider.compute(
                            propViolating, orReversed, initNode, stateSig.getTopVariableHandle());
            final var valuations =
                    mddTrace.stream()
                            .map(
                                    it ->
                                            PathUtils.extractValuation(
                                                    MddValuationCollector.collect(it).stream()
                                                            .findFirst()
                                                            .orElseThrow(),
                                                    0))
                            .toList();
            final List<S> states = new ArrayList<>();
            final List<A> actions = new ArrayList<>();
            for (int i = 0; i < valuations.size(); ++i) {
                states.add(valToState.apply(valuations.get(i)));
                if (i > 0) {
                    actions.add(biValToAction.apply(valuations.get(i - 1), valuations.get(i)));
                }
            }

            if (forwardTrace) {
                result =
                        SafetyResult.unsafe(
                                Trace.of(states, actions), MddProof.of(stateSpace), statistics);
            } else {
                result =
                        SafetyResult.unsafe(
                                Trace.of(Lists.reverse(states), Lists.reverse(actions)),
                                MddProof.of(stateSpace),
                                statistics);
            }
        } else {
            result = SafetyResult.safe(MddProof.of(stateSpace), statistics);
        }
        return result;
    }
}
