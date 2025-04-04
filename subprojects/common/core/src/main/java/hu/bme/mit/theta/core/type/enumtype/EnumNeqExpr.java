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
package hu.bme.mit.theta.core.type.enumtype;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.BinaryExpr;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import java.util.Objects;

public final class EnumNeqExpr extends NeqExpr<EnumType> {

    private static final int HASH_SEED = 7212;
    private static final String OPERATOR_LABEL = "!=";

    private EnumNeqExpr(Expr<EnumType> leftOp, Expr<EnumType> rightOp) {
        super(leftOp, rightOp);
    }

    public static EnumNeqExpr of(Expr<EnumType> leftOp, Expr<EnumType> rightOp) {
        return new EnumNeqExpr(leftOp, rightOp);
    }

    @Override
    public BinaryExpr<EnumType, BoolType> with(Expr<EnumType> leftOp, Expr<EnumType> rightOp) {
        if (leftOp == getLeftOp() && rightOp == getRightOp()) {
            return this;
        } else {
            return EnumNeqExpr.of(leftOp, rightOp);
        }
    }

    @Override
    public BinaryExpr<EnumType, BoolType> withLeftOp(Expr<EnumType> leftOp) {
        return with(leftOp, getRightOp());
    }

    @Override
    public BinaryExpr<EnumType, BoolType> withRightOp(Expr<EnumType> rightOp) {
        return with(getLeftOp(), rightOp);
    }

    @Override
    protected int getHashSeed() {
        return HASH_SEED;
    }

    @Override
    public String getOperatorLabel() {
        return OPERATOR_LABEL;
    }

    @Override
    public BoolType getType() {
        return Bool();
    }

    @Override
    public LitExpr<BoolType> eval(Valuation val) {
        return EnumLitExpr.neq(
                (EnumLitExpr) getLeftOp().eval(val), (EnumLitExpr) getRightOp().eval(val));
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj != null && this.getClass() == obj.getClass()) {
            final EnumNeqExpr that = (EnumNeqExpr) obj;
            return Objects.equals(this.getLeftOp(), that.getLeftOp())
                    && Objects.equals(this.getRightOp(), that.getRightOp());
        } else {
            return false;
        }
    }
}
