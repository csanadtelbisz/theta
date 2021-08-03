package hu.bme.mit.theta.xcfa.transformation.model.types.complex.real;

import hu.bme.mit.theta.xcfa.transformation.model.types.simple.CSimpleType;

public class CFloat extends CReal {
	private static final int RANK = 10;
	public CFloat(CSimpleType origin) {
		super(origin);
		rank = RANK;
	}

	public <T, R> R accept(CComplexTypeVisitor<T, R> visitor, T param) {
		return visitor.visit(this, param);
	}
}