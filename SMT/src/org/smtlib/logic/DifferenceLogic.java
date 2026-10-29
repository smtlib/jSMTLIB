package org.smtlib.logic;

import java.util.Collection;

import org.smtlib.IExpr;
import org.smtlib.ISort;
import org.smtlib.IVisitor;
import org.smtlib.SMT;
import org.smtlib.Utils;
import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.IQualifiedIdentifier;
import org.smtlib.IExpr.ISymbol;

/** Common base for the difference logics QF_IDL and QF_RDL. Their :language allows closed
 *  quantifier-free formulas built with the Core connectives over Bool atoms and restricted
 *  arithmetic atoms (op a b), where op is &lt;, &lt;=, &gt;, &gt;=, = or distinct. A subclass checks
 *  the shape of each arithmetic atom. */
public abstract class DifferenceLogic extends Logic {

    public DifferenceLogic(SMT.Configuration smtConfig, ISymbol name, Collection<IAttribute<?>> attributes) {
        super(smtConfig,name,attributes);
    }

    /** "IDL" or "RDL", for error messages */
    protected abstract String kind();

    /** Checks the arguments of a binary arithmetic atom (op lhs rhs). */
    protected abstract void checkAtom(IExpr.IFcnExpr atom, IExpr lhs, IExpr rhs) throws IVisitor.VisitorException;

    @Override
    public void validExpression(IExpr expression) throws IVisitor.VisitorException {
        noQuantifiers(expression);
        IVisitor<Void> visitor = new IVisitor.TreeVisitor<Void>() {
            @Override
            public Void visit(IExpr.IFcnExpr e) throws IVisitor.VisitorException {
                IQualifiedIdentifier fcn = e.head();
                boolean eq = Utils.EQ.equals(fcn) || Utils.DISTINCT.equals(fcn);
                // Core connectives, including ite, = and distinct over Bool: check the operands
                if (Utils.AND.equals(fcn) || Utils.OR.equals(fcn) || Utils.NOT.equals(fcn)
                        || Utils.IMPLIES.equals(fcn) || Utils.XOR.equals(fcn)
                        || (Utils.ITE.equals(fcn) && isBool(e))
                        || (eq && isBool(e.args().get(0)))) {
                    return super.visit(e);
                }
                if (e.args().size() == 2 && (eq || Utils.GE.equals(fcn) || Utils.GT.equals(fcn)
                        || Utils.LT.equals(fcn) || Utils.LE.equals(fcn))) {
                    checkAtom(e, e.args().get(0), e.args().get(1));
                    return null;
                }
                throw restrictionError("Invalid operation in " + kind() + " logic", e);
            }
        };
        expression.accept(visitor);
    }

    private static boolean isBool(IExpr e) {
        ISort s = e.sort();
        return s != null && s.isBool();
    }

    /** True for (- x y) with x and y symbols */
    protected static boolean isDifferenceOfSymbols(IExpr e) {
        if (!(e instanceof IExpr.IFcnExpr)) return false;
        IExpr.IFcnExpr f = (IExpr.IFcnExpr) e;
        return Utils.MINUS.equals(f.head()) && f.args().size() == 2
                && f.args().get(0) instanceof ISymbol && f.args().get(1) instanceof ISymbol;
    }
}
