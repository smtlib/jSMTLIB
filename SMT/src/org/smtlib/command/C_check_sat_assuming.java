/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.command;

import java.io.IOException;
import java.util.List;

import org.smtlib.ICommand.Icheck_sat_assuming;
import org.smtlib.IParser.ParserException;
import org.smtlib.SMT.Configuration.SMTLIB;
import org.smtlib.IExpr;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.IVisitor;
import org.smtlib.SMT;
import org.smtlib.impl.Command;
import org.smtlib.sexpr.Parser;
import org.smtlib.sexpr.Printer;

/** Implements the check-sat command */
public class C_check_sat_assuming extends Command implements Icheck_sat_assuming {
	/** Creates a check_sat_assuming command (which has no arguments) */
	public C_check_sat_assuming(List<IExpr> terms) {
	    this.terms = terms;
	}
	
	/** Parses the arguments of the command, producing a new command instance */
	static public /*@Nullable*/ C_check_sat_assuming parse(Parser p) throws ParserException {
//		if (SMT.Configuration.isVersion(SMTLIB.V20)) {
//			p.error("The check-sat-assuming command is not valid in V2.0", p.peekToken().pos());
//			return null;
//		}
        List<IExpr> list = p.parseListTerms(p);
		return new C_check_sat_assuming(list);
	}

    /** The terms whose values are to be gotten */
    protected List<IExpr> terms;

	/** The command name */
	public static final String commandName = "check-sat-assuming";
	
	/** The command name */
	@Override
	public String commandName() { return commandName; }
	
    /** The terms whose values are to be gotten */
    @Override
    public List<IExpr> exprs() { return terms; }

	@Override
	public void writeArgs(Printer p) throws IOException, IVisitor.VisitorException {
        p.writer().append(" (");
        for (IExpr e: exprs()) {
            p.writer().append(" ");
            e.accept(p);
        }
        p.writer().append(")");
	}
	
	@Override
	public IResponse execute(ISolver solver) {
		return solver.check_sat_assuming();
	}

	@Override
	public <T> T accept(IVisitor<T> v) throws IVisitor.VisitorException {
		return v.visit(this);
	}
}
