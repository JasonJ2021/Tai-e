/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis.constprop;

import org.checkerframework.checker.units.qual.A;
import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.Binary;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;
import soot.jimple.internal.AbstractBinopExpr;

import java.util.concurrent.locks.Condition;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        CPFact ans = new CPFact();
        for (Var v : cfg.getIR().getParams()) {
            if (canHoldInt(v)) {
                ans.update(v, Value.getNAC());
            }
        }
        return ans;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me\
        // All variable is undefine , -> unsafe
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        // fact<Var , Value>
        for (Var var : fact.keySet()) {
            target.update(var, meetValue(fact.get(var), target.get(var)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        // corresponding meet opeartion
        // NAC meet other = NAC
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }
        // UNDEF meet other v = v
        if (v1.isUndef()) {
            return v2;
        } else if (v2.isUndef()) {
            return v1;
        }
        if (v1.equals(v2)) {
            return v1;
        }
        return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        if (stmt.getDef().isEmpty() || !(stmt.getDef().get() instanceof Var)) {
            return out.copyFrom(in);
        }
        Var x = (Var) stmt.getDef().get();
        if (!canHoldInt(x)) {
            return out.copyFrom(in);
        }
        Value value = evaluate((Exp) (stmt.getUses().get(stmt.getUses().size() - 1)), in);
        CPFact in_copy = in.copy();
        in_copy.remove(x);
        in_copy.update(x, value);
        return out.copyFrom(in_copy);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
        if (exp instanceof Var) {
            return in.get((Var) exp);
        }
        if (exp instanceof IntLiteral) {
            int value = ((IntLiteral) exp).getValue();
            return Value.makeConstant(value);
        }
        if (!check_exprType(exp)) {
            return Value.getNAC();
        }
        Value x = in.get(((BinaryExp) exp).getOperand1());
        Value y = in.get(((BinaryExp) exp).getOperand2());
        // x = a / 0 , x is UNDEF even if a is nac
        if(x.isNAC() && y.isConstant() && y.getConstant() == 0){
            if(exp instanceof  ArithmeticExp){
                ArithmeticExp.Op op = ((ArithmeticExp)exp).getOperator();
                if(op == ArithmeticExp.Op.REM || op == ArithmeticExp.Op.DIV){
                    return Value.getUndef();
                }
            }
        }
        if (x.isNAC() || y.isNAC()) {
            return Value.getNAC();
        }
        if (x.isUndef() || y.isUndef()) {
            return Value.getUndef();
        }
        int x_const = x.getConstant();
        int y_const = y.getConstant();
        if (exp instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) exp).getOperator();
            return evaluateArith(op, x_const, y_const);
        }
        if (exp instanceof BitwiseExp) {
            BitwiseExp.Op op = ((BitwiseExp) exp).getOperator();
            return evaluateBitWise(op, x_const, y_const);
        }
        if (exp instanceof ConditionExp) {
            ConditionExp.Op op = ((ConditionExp) exp).getOperator();
            return evaluateCond(op, x_const, y_const);
        }
        if (exp instanceof ShiftExp) {
            ShiftExp.Op op = ((ShiftExp) exp).getOperator();
            return evaluateShift(op, x_const, y_const);
        }
        return Value.getNAC();
    }

    private static boolean check_exprType(Exp exp) {
        return (exp instanceof Var) || (exp instanceof IntLiteral) || (exp instanceof ArithmeticExp) || (exp instanceof ConditionExp)
                || (exp instanceof ShiftExp) || (exp instanceof BitwiseExp)  ;
    }

    private static Value evaluateShift(ShiftExp.Op op, int x, int y) {
        Value value = null;
        switch (op) {
            case SHL: {
                value = Value.makeConstant(x << y);
                break;
            }
            case SHR: {
                value = Value.makeConstant(x >> y);
                break;
            }
            case USHR: {
                value = Value.makeConstant(x >>> y);
                break;
            }
        }
        return value;
    }

    private static Value evaluateCond(ConditionExp.Op op, int x, int y) {
        Value value = null;
        switch (op) {
            case EQ: {
                value = Value.makeConstant(x == y ? 1 : 0);
                break;
            }
            case NE: {
                value = Value.makeConstant(x != y ? 1 : 0);
                break;
            }
            case LT: {
                value = Value.makeConstant(x < y ? 1 : 0);
                break;
            }
            case GT: {
                value = Value.makeConstant(x > y ? 1 : 0);
                break;
            }
            case LE: {
                value = Value.makeConstant(x <= y ? 1 : 0);
                break;
            }
            case GE: {
                value = Value.makeConstant(x >= y ? 1 : 0);
                break;
            }
        }
        return value;
    }

    private static Value evaluateBitWise(BitwiseExp.Op op, int x, int y) {
        Value value = null;
        switch (op) {
            case OR: {
                value = Value.makeConstant(x | y);
                break;
            }
            case XOR: {
                value = Value.makeConstant(x ^ y);
                break;
            }
            case AND: {
                value = Value.makeConstant(x & y);
                break;
            }
        }
        return value;
    }

    private static Value evaluateArith(ArithmeticExp.Op op, int x, int y) {
        Value value = null;
        switch (op) {
            case ADD: {
                value = Value.makeConstant(x + y);
                break;
            }
            case SUB: {
                value = Value.makeConstant(x - y);
                break;
            }
            case MUL: {
                value = Value.makeConstant(x * y);
                break;
            }
            case REM: {
                if (y == 0) return Value.getUndef();
                value = Value.makeConstant(x % y);
                break;
            }
            case DIV: {
                if (y == 0) return Value.getUndef();
                value = Value.makeConstant(x / y);
                break;
            }
        }
        return value;
    }
}
