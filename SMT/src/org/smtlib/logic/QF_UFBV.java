package org.smtlib.logic;

import java.util.Collection;

import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.ISymbol;

/** Quantifier-free, with uninterpreted functions and sorts permitted -- identical
 *  restrictions to QF_UF, all inherited from it (the bit-vector vs. plain-UF distinction is
 *  carried entirely by the bundled theory signature, not by any extra syntactic restriction
 *  here). */
public class QF_UFBV extends QF_UF {

	public QF_UFBV(ISymbol name, Collection<IAttribute<?>> attributes) {
		super(name,attributes);
	}

}
