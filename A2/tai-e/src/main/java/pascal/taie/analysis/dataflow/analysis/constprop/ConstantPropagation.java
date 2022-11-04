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

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import static pascal.taie.ir.exp.ArithmeticExp.Op.*;

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
        // Initialize all the parameters to NAC
        CPFact boundaryFact = new CPFact();
        for (Var param : cfg.getIR().getParams()) {
            if (canHoldInt(param)) {
                boundaryFact.update(param, Value.getNAC());
            }
        }
        return boundaryFact;
    }

    @Override
    public CPFact newInitialFact() {
        CPFact initialFact = new CPFact();
        return initialFact;
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        for (Var var: fact.keySet()) {
            if (canHoldInt(var)) {
                target.update(var, meetValue(fact.get(var), target.get(var)));
            }
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // NAC meet v = NAC
        // UNDEF meet v = v
        // c meet c = c
        // c1 meet c2 = NAC
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        } else if (v1.isUndef() && v2.isConstant()) {
            return v2;
        } else if (v1.isConstant() && v2.isUndef()) {
            return v1;
        } else if (v1.equals(v2)) {
            return v1;
        } else {
            return Value.getNAC();
        }
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        out.copyFrom(in);
        // OUT[s] = gen \wedge (IN[s] - {x, _})
        if (stmt instanceof DefinitionStmt) {
            LValue lValue = ((DefinitionStmt<?, ?>) stmt).getLValue();
            RValue rValue = ((DefinitionStmt<?, ?>) stmt).getRValue();

            // TypeCheck
            // lValue must be var
            // and rValue must be {constant || var || binaryExp}
            if (!(lValue instanceof Var)) {
                return false;
            } else if (!canHoldInt((Var) lValue)) {
                return false;
            }

            // transferFunction
            out.update((Var) lValue, evaluate(rValue, in));
            return true;
        }
        return false;
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
                default:
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
        // evaluate(rValue, in)
        // use rValue to replace the old rValue in [in]
        if (exp instanceof IntLiteral) {
            int constVal = ((IntLiteral) exp).getValue();
            return Value.makeConstant(constVal);
        } else if (exp instanceof Var) {
            return in.get((Var) exp);
        } else if (exp instanceof BinaryExp) {
            BinaryExp.Op op = ((BinaryExp) exp).getOperator();
            Value lVal = in.get(((BinaryExp) exp).getOperand1());
            Value rVal = in.get(((BinaryExp) exp).getOperand2());

            // if val(y) and val(z) are constants
            // return val(y) op val(z)
            if (lVal.isConstant() && rVal.isConstant()) {
                int v1 = lVal.getConstant();
                int v2 = rVal.getConstant();

                if (exp instanceof ArithmeticExp) {
                    return switch ((ArithmeticExp.Op) op) {
                        case ADD -> Value.makeConstant(v1 + v2);
                        case SUB -> Value.makeConstant(v1 - v2);
                        case MUL -> Value.makeConstant(v1 * v2);
                        case DIV -> v2 == 0 ? Value.getUndef() : Value.makeConstant(v1 / v2);
                        case REM -> Value.makeConstant(v1 % v2);
                    };
                } else if (exp instanceof ConditionExp) {
                    return switch ((ConditionExp.Op) op) {
                        case EQ -> v1 == v2 ? Value.makeConstant(1) : Value.makeConstant(0);
                        case NE -> v1 != v2 ? Value.makeConstant(1) : Value.makeConstant(0);
                        case LT -> v1 < v2 ? Value.makeConstant(1) : Value.makeConstant(0);
                        case GT -> v1 > v2 ? Value.makeConstant(1) : Value.makeConstant(0);
                        case LE -> v1 <= v2 ? Value.makeConstant(1) : Value.makeConstant(0);
                        case GE -> v1 >= v2 ? Value.makeConstant(1) : Value.makeConstant(0);
                    };
                } else if (exp instanceof ShiftExp) {
                    return switch ((ShiftExp.Op) op) {
                        case SHL -> Value.makeConstant(v1 << v2);
                        case SHR -> Value.makeConstant(v1 >> v2);
                        case USHR -> Value.makeConstant(v1 >>> v2);
                    };
                } else if (exp instanceof BitwiseExp) {
                    return switch ((BitwiseExp.Op) op) {
                        case OR -> Value.makeConstant(v1 | v2);
                        case AND -> Value.makeConstant(v1 & v2);
                        case XOR -> Value.makeConstant(v1 ^ v2);
                    };
                }
            }
            // if val(y) is NAC or val(z) is NAC
            // return NAC
            else if (lVal.isNAC() || rVal.isNAC()) {
                return Value.getNAC();
            }
            // otherwise
            // return Undef
            else {
                return Value.getUndef();
            }
        }
        return Value.getNAC();
    }
}
