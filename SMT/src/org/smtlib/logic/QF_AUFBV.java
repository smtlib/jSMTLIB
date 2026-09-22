package org.smtlib.logic;

import org.smtlib.SMT;

import java.util.Collection;

import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.ISymbol;

/** This logic does not allow quantifiers */
public class QF_AUFBV extends QF_UF {

	public QF_AUFBV(SMT.Configuration smtConfig, ISymbol name, Collection<IAttribute<?>> attributes) {
		super(smtConfig,name,attributes);
	}
	
	// FIXME - needs restriction on parameters of Array Sorts
}
