package hu.bme.mit.theta.cat.solver;

public abstract class MemoryModel {
	public void applyRules(final MemoryModelBuilder memoryModelBuilder) {
		memoryModelBuilder.addRule(new RuleDerivation.Element("poRaw", 2));
		memoryModelBuilder.addRule(new RuleDerivation.Element("intRaw", 2));
		memoryModelBuilder.addRule(new RuleDerivation.Element("amoRaw", 2));
		memoryModelBuilder.addRule(new RuleDerivation.Element("locRaw", 2));

		memoryModelBuilder.addRule(new RuleDerivation.Element("meta", 1));
		memoryModelBuilder.addRule(new RuleDerivation.Element("W", 1));
		memoryModelBuilder.addRule(new RuleDerivation.Element("R", 1));
		memoryModelBuilder.addRule(new RuleDerivation.Element("F", 1));
		memoryModelBuilder.addRule(new RuleDerivation.Union("M", new RuleDerivation.Element("W", 1), new RuleDerivation.Element("R", 1)));
		memoryModelBuilder.addRule(new RuleDerivation.Union("U", new RuleDerivation.Element("M", 1), new RuleDerivation.Element("F", 1)));
		memoryModelBuilder.addRule(new RuleDerivation.CartesianProduct("UB", new RuleDerivation.Element("U", 1), new RuleDerivation.Element("U", 1)));

		memoryModelBuilder.addRule(new RuleDerivation.Element("id", 2));
		memoryModelBuilder.addRule(new RuleDerivation.Element("rf", 2));
		memoryModelBuilder.addRule(new RuleDerivation.Element("co", 2));
		memoryModelBuilder.addRule(new RuleDerivation.Transitive("po", new RuleDerivation.Element("poRaw", 2)));
		memoryModelBuilder.addRule(new RuleDerivation.Transitive("int", new RuleDerivation.Element("intRaw", 2)));
		memoryModelBuilder.addRule(new RuleDerivation.Transitive("loc", new RuleDerivation.Element("locRaw", 2)));
		memoryModelBuilder.addRule(new RuleDerivation.Transitive("amo", new RuleDerivation.Element("amoRaw", 2)));
		memoryModelBuilder.addRule(new RuleDerivation.Difference("ext", new RuleDerivation.Element("UB", 2), new RuleDerivation.Element("int", 2)));
		memoryModelBuilder.addRule(new RuleDerivation.Consecutive("fr", new RuleDerivation.Inverse("fr1", new RuleDerivation.Element("rf", 2)), new RuleDerivation.Element("co", 2)));
	}
}
