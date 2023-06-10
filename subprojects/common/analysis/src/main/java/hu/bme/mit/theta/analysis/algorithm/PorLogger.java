package hu.bme.mit.theta.analysis.algorithm;

import java.util.ArrayList;
import java.util.List;

public class PorLogger {
	public static List<Integer> exploredActions = new ArrayList<>();
	public static List<Long> exploredStates = new ArrayList<>();
	public static List<Long> preservedStates = new ArrayList<>();
	public static List<DependencyRelationSizeEntry> dependencyRelationSize = new ArrayList<>();

	public static void exploreAction() {
		exploredActions.set(exploredActions.size() - 1, exploredActions.get(exploredActions.size() - 1) + 1);
	}

	public static class DependencyRelationSizeEntry {
		public DependencyRelationSizeEntry(Long allPairs, Long dependentTraditional, Long dependentAbstraction) {
			this.allPairs = allPairs;
			this.dependentTraditional = dependentTraditional;
			this.dependentAbstraction = dependentAbstraction;
		}

		public Long allPairs;
		public Long dependentTraditional;
		public Long dependentAbstraction;

		@Override
		public String toString() {
			return "[" + allPairs + "," + dependentTraditional + "," + dependentAbstraction + "]";
		}
	}
}
