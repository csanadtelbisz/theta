/*
 *  Copyright 2017 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.expr.refinement;

import com.google.common.base.Stopwatch;
import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.IndexedVars;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.solver.Interpolant;
import hu.bme.mit.theta.solver.ItpMarker;
import hu.bme.mit.theta.solver.ItpPattern;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.utils.WithPushPop;;

import java.time.temporal.ChronoUnit;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import static com.google.common.base.Preconditions.checkNotNull;

/**
 * An ExprTraceChecker that uses no interpolation, nor unsat cores
 * Used to check feasibility of concretizable traces
 */
public final class ExprTraceNoItpChecker implements ExprTraceChecker<Refutation> {

	private final Solver solver;
	private final Expr<BoolType> init;
	private final Expr<BoolType> target;

	private ExprTraceNoItpChecker(final Expr<BoolType> init, final Expr<BoolType> target, final Solver solver) {
		this.solver = checkNotNull(solver);
		this.init = checkNotNull(init);
		this.target = checkNotNull(target);
	}

	public static ExprTraceNoItpChecker create(final Expr<BoolType> init, final Expr<BoolType> target,
											   final Solver solver) {
		return new ExprTraceNoItpChecker(init, target, solver);
	}

	@Override
	public ExprTraceStatus<Refutation> check(final Trace<? extends ExprState, ? extends ExprAction> trace) {
		Stopwatch stopwatch = Stopwatch.createStarted();
		checkNotNull(trace);
		final int stateCount = trace.getStates().size();

		final List<VarIndexing> indexings = new ArrayList<>(stateCount);
		indexings.add(VarIndexingFactory.indexing(0));

		solver.push();

		int nPush = 1;
		solver.add(PathUtils.unfold(init, indexings.get(0)));
		solver.add(PathUtils.unfold(trace.getState(0).toExpr(), indexings.get(0)));
		assert solver.check().isSat() : "Initial state of the trace is not feasible";
		int satPrefix = 0;

		for (int i = 1; i < stateCount; ++i) {
			solver.push();
			++nPush;
			indexings.add(indexings.get(i - 1).add(trace.getAction(i - 1).nextIndexing()));
			solver.add(PathUtils.unfold(trace.getState(i).toExpr(), indexings.get(i)));
			solver.add(PathUtils.unfold(trace.getAction(i - 1).toExpr(), indexings.get(i - 1)));

			/*
			if (solver.check().isSat()) {
				satPrefix = i;
			} else {
				solver.pop();
				--nPush;
				break;
			}
			*/
		}


		final boolean concretizable;
		stopwatch.stop();
		System.err.println(stopwatch.elapsed().get(ChronoUnit.SECONDS));

		stopwatch = Stopwatch.createStarted();
		if (solver.check().isSat()) {
			concretizable = true;
		} else {
			concretizable = false;
		}
		stopwatch.stop();
		System.err.println(stopwatch.elapsed().get(ChronoUnit.SECONDS));
/*
		if (satPrefix == stateCount - 1) {
			solver.add(PathUtils.unfold(target, indexings.get(stateCount - 1)));
			concretizable = solver.check().isSat();
		} else {
			solver.add(PathUtils.unfold(trace.getState(satPrefix + 1).toExpr(), indexings.get(satPrefix + 1)));
			solver.add(PathUtils.unfold(trace.getAction(satPrefix).toExpr(), indexings.get(satPrefix)));
			solver.check();
			assert solver.getStatus().isUnsat() : "Trying to interpolate a feasible formula";
			concretizable = false;
		}
*/

		ExprTraceStatus<Refutation> status = null;
		if (concretizable) {
			final Valuation model = solver.getModel();
			final ImmutableList.Builder<Valuation> builder = ImmutableList.builder();
			for (final VarIndexing indexing : indexings) {
				builder.add(PathUtils.extractValuation(model, indexing));
			}
			return ExprTraceStatus.feasible(Trace.of(builder.build(), trace.getActions()));
		} else {
			throw new RuntimeException("Trace should be concretizable!");
		}
	}

	@Override
	public String toString() {
		return getClass().getSimpleName();
	}

}
