package org.smtlib.logic;

import org.smtlib.SMT;

import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import org.smtlib.*;
import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.IIdentifier;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IExpr.ISymbol;

public class QF_UFIDL extends Logic {

    public QF_UFIDL(SMT.Configuration smtConfig, ISymbol name, Collection<IAttribute<?>> attributes) {
        super(smtConfig,name,attributes);
    }

    /** Int symbols outside the logic's signature (its :language lists numerals, binary - and +,
     *  {@code <=, <, >=, >}) */
    private static final List<String> NOT_ALLOWED = Arrays.asList("*", "**", "div", "mod", "abs", "divisible");

    /** QF_UFIDL's :language: no quantifiers; Int symbols as above; and "for every term of the
     *  form (op t1 t2) with op in {+, -}, at least one of t1 and t2 is a numeral". Its :note
     *  says the syntax is not an extension of QF_IDL's, so QF_IDL's atom shapes do not apply. */
    @Override
    public void validExpression(IExpr expression) throws IVisitor.VisitorException {
        noQuantifiers(expression);
        IVisitor<Void> visitor = new IVisitor.TreeVisitor<Void>() {
            @Override
            public Void visit(IExpr.IFcnExpr e) throws IVisitor.VisitorException {
                ISymbol head = e.head().headSymbol();
                if (Utils.PLUS.equals(head) || Utils.MINUS.equals(head)) {
                    List<IExpr> args = e.args();
                    if (args.size() < 2) throw restrictionError("Negation is not allowed in the QF_UFIDL logic", e);
                    // (op t1 t2 ... tn) is (op ... (op t1 t2) ... tn) (:left-assoc)
                    boolean ok = args.get(0) instanceof INumeral || args.get(1) instanceof INumeral;
                    for (int i = 2; i < args.size(); i++) ok &= args.get(i) instanceof INumeral;
                    if (!ok) throw restrictionError("In each (+ t1 t2) or (- t1 t2), t1 or t2 must be a numeral in the QF_UFIDL logic", e);
                } else if (NOT_ALLOWED.contains(head.value())) {
                    throw restrictionError("The function symbol " + head.value() + " is not allowed in the QF_UFIDL logic", e);
                }
                return super.visit(e);
            }
        };
        expression.accept(visitor);
    }

    public void checkFcnDeclaration(IExpr.IIdentifier id, List<ISort> argSorts, ISort resultSort, /*@Nullable*/IExpr definition) throws IVisitor.VisitorException {
    }

    public void checkSortDeclaration(IIdentifier id, List<ISort.IParameter> params, ISort expr) throws IVisitor.VisitorException {
    }

}
