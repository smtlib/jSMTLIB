/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.sexpr;

import java.io.*;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.List;

import org.smtlib.*;
import org.smtlib.ICommand.IScript;
import org.smtlib.IExpr.IAsIdentifier;
import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.IAttributedExpr;
import org.smtlib.IExpr.IBinaryLiteral;
import org.smtlib.IExpr.IBinding;
import org.smtlib.IExpr.IDecimal;
import org.smtlib.IExpr.IDeclaration;
import org.smtlib.IExpr.IExists;
import org.smtlib.IExpr.IFcnExpr;
import org.smtlib.IExpr.IForall;
import org.smtlib.IExpr.IHexLiteral;
import org.smtlib.IExpr.IKeyword;
import org.smtlib.IExpr.ILet;
import org.smtlib.IExpr.IMatch;
import org.smtlib.IExpr.IMatchCase;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IExpr.IPattern;
import org.smtlib.IExpr.IParameterizedIdentifier;
import org.smtlib.IExpr.IStringLiteral;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IResponse.IAssertionsResponse;
import org.smtlib.IResponse.IAssignmentResponse;
import org.smtlib.IResponse.IAttributeList;
import org.smtlib.IResponse.IProofResponse;
import org.smtlib.IResponse.IUnsatCoreResponse;
import org.smtlib.IResponse.IValueResponse;
import org.smtlib.ISort.IAbbreviation;
import org.smtlib.ISort.IApplication;
import org.smtlib.ISort.IFamily;
import org.smtlib.ISort.IFcnSort;
import org.smtlib.ISort.IParameter;

/** This class writes out SMT-LIB ASTs as concrete S-expression syntax; aside from white space
 * between tokens it should simply reverse what the Parser class does.  */
public class Printer implements IPrinter, org.smtlib.IVisitor</*@Nullable*/ Void> {

	static public SMT.Configuration smtConfig;

	/** The writer to write text to */
	/*@Nullable*/ protected Writer w;

	/** The writer to write text to */
	public Writer writer() { return w; }

	/** The system-dependent line termination */
	static public final String eol = System.getProperty("line.separator");

	/** Creates a printer object */
	public Printer(Writer w) {
		this.w = w;
	}

	/** Appends a string to the writer, converting any IOException to VisitorException. */
	protected void append(String s) throws IVisitor.VisitorException {
		try { w.append(s); } catch (IOException ex) { throw new IVisitor.VisitorException(ex); }
	}

	/** Flushes the writer, converting any IOException to VisitorException. */
	protected void flush() throws IVisitor.VisitorException {
		try { w.flush(); } catch (IOException ex) { throw new IVisitor.VisitorException(ex); }
	}

	@Override
	public Printer newPrinter(Writer w) {
		return new Printer(w);
	}

	/** Prints the argument to the receiver */
	@Override
	public <T extends INode> void print(T expr) throws IVisitor.VisitorException {
		expr.accept(this);
	}

	/** Returns the argument as a String using a Printer of the same type as the receiver,
	 * but does not modify the receiver.
	 */
	@Override
	public <T extends INode> String toString(T expr) {
		try {
			StringWriter sw = new StringWriter();
			expr.accept(new Printer(sw)); // FIXME = should be same type as receiver
			return sw.toString();
		} catch (IVisitor.VisitorException e) {
			return "<<ERROR: " + e.getMessage() + ">>";
		}
	}

	/** Writes the given expression and outputs as a String */
	static public <T extends INode> String write(T e) {
		try {
			StringWriter w = new StringWriter();
			e.accept(new Printer(w));
			return w.toString();
		} catch (IVisitor.VisitorException ex) {
			return "<<ERROR: " + ex.getMessage() + ">>";
		}
	}

	/** Writes the given expression to the given writer */
	static public <T extends INode> void write(Writer w, T e) throws IVisitor.VisitorException {
		Printer p = new Printer(w);
		e.accept(p);
		p.flush();
	}

	/** Writes the given expression to the given stream */
	static public <T extends INode> void write(PrintStream w, T e) throws IVisitor.VisitorException {
		Writer wr = new OutputStreamWriter(w);
		Printer p = new Printer(wr);
		e.accept(p);
		p.flush();
	}

	/*@Nullable*/
	@Override
	public Void visit(INumeral e) throws IVisitor.VisitorException {
		append(e.value().toString());
		return null;
	}

	/*@Nullable*/
	@Override
	public Void visit(ISymbol e) throws IVisitor.VisitorException { // FIX - need s-expr representation of ids from anywhere
		// FIXME: toString() is correct for parsed symbols but not for programmatically
		// constructed ones with special characters — those need bar-quoting via value().
		append(e.toString());
		return null;
	}

	/*@Nullable*/
	@Override
	public Void visit(IDecimal e) throws IVisitor.VisitorException {
		append(e.value().toPlainString());
		return null;
	}

	@Override
	public Void visit(IBinaryLiteral e) throws IVisitor.VisitorException {
		append("#b");
		append(e.value());
		return null;
	}

	@Override
	public Void visit(IHexLiteral e) throws IVisitor.VisitorException {
		append("#x");
		append(e.value());
		return null;
	}

	/*@Nullable*/
	@Override
	public Void visit(IStringLiteral e) throws IVisitor.VisitorException {
		append(smtConfig.utils.quote(e.value()));
		return null;
	}

	/*@Nullable*/
	@Override
	public Void visit(IKeyword e) throws IVisitor.VisitorException {
		append(e.value());
		return null;
	}

	/*@Nullable*/
	@Override
	public Void visit(org.smtlib.IExpr.IError e) throws IVisitor.VisitorException {
		append("(error ");
		append(smtConfig.utils.quote(e.value()));
		append(")");
		return null;
	}

	@Override
	public Void visit(IParameterizedIdentifier e) throws IVisitor.VisitorException {
		append("(" + Utils.PARAM + " ");
		e.headSymbol().accept(this);
		for (IExpr.IIndex idx: e.indices()) {
			append(" ");
			idx.accept(this);
		}
		append(")");
		return null;
	}

	@Override
	public Void visit(IAsIdentifier e) throws IVisitor.VisitorException {
		append("(" + Utils.AS + " ");
		e.head().accept(this);
		append(" ");
		e.qualifier().accept(this);
		append(")");
		return null;
	}

	@Override
	public Void visit(IFcnExpr e) throws IVisitor.VisitorException {
		append("(");
		e.head().accept(this);
		for (IExpr a: e.args()) {
			append(" ");
			if (a != null) a.accept(this);
			else append("???");
		}
		append(")");
		return null;
	}

	@Override
	public Void visit(IForall e) throws IVisitor.VisitorException {
		append("(" + Utils.FORALL + " (");
		for (IDeclaration a: e.parameters()) {
			a.accept(this);
			append(" ");
		}
		append(") ");
		e.expr().accept(this);
		append(")");
		return null;
	}

	@Override
	public Void visit(IExists e) throws IVisitor.VisitorException {
		append("(" + Utils.EXISTS + " (");
		for (IDeclaration a: e.parameters()) {
			a.accept(this);
			append(" ");
		}
		append(") ");
		e.expr().accept(this);
		append(")");
		return null;
	}

	@Override
	public Void visit(ILet e) throws IVisitor.VisitorException {
		append("(" + Utils.LET + " (");
		for (IBinding a: e.bindings()) {
			a.accept(this);
			append(" ");
		}
		append(") ");
		e.expr().accept(this);
		append(")");
		return null;
	}

	@Override
	public Void visit(IExpr.IMatch e) throws IVisitor.VisitorException {
		append("(match ");
		e.expr().accept(this);
		append(" (");
		for (IExpr.IMatchCase mc : e.cases()) {
			append(" ");
			mc.accept(this);
		}
		append("))");
		return null;
	}

	@Override
	public Void visit(IExpr.IMatchCase e) throws IVisitor.VisitorException {
		append("(");
		e.pattern().accept(this);
		append(" ");
		e.body().accept(this);
		append(")");
		return null;
	}

	@Override
	public Void visit(IExpr.IPattern e) throws IVisitor.VisitorException {
		if (e.params().isEmpty()) {
			e.constructor().accept(this);
		} else {
			append("(");
			e.constructor().accept(this);
			for (IExpr.ISymbol v : e.params()) {
				append(" ");
				v.accept(this);
			}
			append(")");
		}
		return null;
	}

	@Override
	public Void visit(IAttribute<? extends IAttributeValue> e) throws IVisitor.VisitorException {
		/*@Nullable*/IAttributeValue o;
		e.keyword().accept(this);
		if ((o=e.attrValue()) != null) {
			append(" ");
			o.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(IAttributedExpr e) throws IVisitor.VisitorException {
		append("(" + Utils.ATTRIBUTE + " ");
		e.expr().accept(this);
		for (IAttribute<?> a: e.attributes()) {
			append(" ");
			a.accept(this);
		}
		append(")");
		return null;
	}

	@Override
	public Void visit(IDeclaration e) throws IVisitor.VisitorException {
		append("(");
		e.parameter().accept(this);
		append(" ");
		e.sort().accept(this);
		append(")");
		return null;
	}

	@Override
	public Void visit(IExpr.IFunctionDeclaration e) throws IVisitor.VisitorException {
		append("(");
		e.symbol().accept(this);
		append(" (");
		for (IExpr.IDeclaration d : e.parameters()) { d.accept(this); append(" "); }
		append(") ");
		e.sort().accept(this);
		append(")");
		return null;
	}

	@Override
	public Void visit(IExpr.ISortDeclaration e) throws IVisitor.VisitorException {
		append("(");
		e.symbol().accept(this);
		append(" ");
		e.arity().accept(this);
		append(")");
		return null;
	}

	@Override
	public Void visit(IExpr.ISelector e) throws IVisitor.VisitorException {
		append("(");
		e.symbol().accept(this);
		append(" ");
		e.sort().accept(this);
		append(")");
		return null;
	}

	@Override
	public Void visit(IExpr.IConstructor e) throws IVisitor.VisitorException {
		append("(");
		e.symbol().accept(this);
		for (IExpr.ISelector s : e.selectors()) { append(" "); s.accept(this); }
		append(")");
		return null;
	}

	@Override
	public Void visit(IBinding e) throws IVisitor.VisitorException {
		append("(");
		e.parameter().accept(this);
		append(" ");
		e.expr().accept(this);
		append(")");
		return null;
	}

	@Override
	public Void visit(IScript e) throws IVisitor.VisitorException {
		IStringLiteral filename = e.filename();
		List<ICommand> commands = e.commands();
		if (filename != null) {
			filename.accept(this);
		} else if (commands != null) {
			append("(");
			append(eol);
			for (ICommand c: commands) {
				c.accept(this);
				append(eol);
				flush();
			}
			append(")");
		} else {
			append("\"<ERROR: Script has no content>\"");
		}
		return null;
	}

	public static class WithLines extends Printer {

		/** Creates a printer object */
		public WithLines(Writer w) {
			super(w);
		}

		@Override
		public WithLines newPrinter(Writer w) {
			return new WithLines(w);
		}

		/** Writes the given expression to the given stream */
		static public <T extends INode> void write(PrintStream w, T e) throws IVisitor.VisitorException {
			Writer wr = new OutputStreamWriter(w);
			WithLines p = new WithLines(wr);
			e.accept(p);
			p.flush();
		}

		@Override
		public Void visit(IScript e) throws IVisitor.VisitorException {
			int n = 0;
			IStringLiteral filename = e.filename();
			List<ICommand> commands = e.commands();
			if (filename != null) {
				filename.accept(this);
			} else if (commands != null) {
				append("(");
				append(eol);
				for (ICommand c: commands) {
					append((++n) + ": ");
					c.accept(this);
					append(eol);
					flush();
				}
				append(")");
			} else {
				append("\"<ERROR: Script has no content>\"");
			}
			return null;
		}


	}

	/** Functional interface for the argument-printing lambda passed to {@link #printCommand}. */
	@FunctionalInterface
	protected interface PrintArgs {
		void run() throws IVisitor.VisitorException;
	}

	/** Prints {@code (commandName() args)} — the space between name and args is emitted here,
	 *  so the {@code args} lambda should not prepend one. Subclasses may override to
	 *  change the overall command format. */
	protected Void printCommand(ICommand e, PrintArgs args) throws IVisitor.VisitorException {
		append("(" + e.commandName() + " ");
		args.run();
		append(")");
		return null;
	}

	/** Prints a no-argument command: {@code (commandName())}. Subclasses may override to change format. */
	protected Void printCommand(ICommand e) throws IVisitor.VisitorException {
		append("(" + e.commandName() + ")");
		return null;
	}

	/** Fallback for extension command types not covered by a specific visit method;
	 *  uses reflection to invoke {@code write(Printer)} on the command object. */
	@Override
	public Void visit(ICommand e) throws IVisitor.VisitorException {
		Class<?> clazz = e.getClass();
		try {
			Method m = clazz.getMethod("write", Printer.class);
			m.invoke(e, this);
		} catch (IllegalAccessException ex) {
			throw new IVisitor.VisitorException(ex,
					e instanceof IPos.IPosable ? ((IPos.IPosable)e).pos() : null);
		} catch (InvocationTargetException ex) {
			throw new IVisitor.VisitorException(ex.getTargetException(),
					e instanceof IPos.IPosable ? ((IPos.IPosable)e).pos() : null);
		} catch (NoSuchMethodException ex) {
			throw new IVisitor.VisitorException(
					"No write method for " + clazz + " and " + this.getClass(), null);
		}
		return null;
	}

	@Override
	public Void visit(ICommand.Iassert e) throws IVisitor.VisitorException {
		return printCommand(e, () -> e.expr().accept(this));
	}

	@Override
	public Void visit(ICommand.Icheck_sat e) throws IVisitor.VisitorException {
		return printCommand(e);
	}

	@Override
	public Void visit(ICommand.Icheck_sat_assuming e) throws IVisitor.VisitorException {
		return printCommand(e, () -> {
			append("(");
			for (IExpr x : e.terms()) { append(" "); x.accept(this); }
			append(")");
		});
	}

	@Override
	public Void visit(ICommand.Ideclare_const e) throws IVisitor.VisitorException {
		return printCommand(e, () -> {
			e.symbol().accept(this);
			append(" ");
			e.resultSort().accept(this);
		});
	}

	@Override
	public Void visit(ICommand.Ideclare_datatype e) throws IVisitor.VisitorException {
		return printCommand(e, () -> {
			e.sortDeclaration().symbol().accept(this);
			append(" ");
			e.datatype().accept(this);
		});
	}

	@Override
	public Void visit(ICommand.Ideclare_datatypes e) throws IVisitor.VisitorException {
		return printCommand(e, () -> {
			append("(");
			for (IExpr.ISortDeclaration sd : e.sortDeclarations()) { append(" "); sd.accept(this); }
			append(") (");
			for (ISort.IDatatype dt : e.datatypes()) { append(" "); dt.accept(this); }
			append(")");
		});
	}

	@Override
	public Void visit(ICommand.Ideclare_fun e) throws IVisitor.VisitorException {
		return printCommand(e, () -> {
			e.symbol().accept(this);
			append(" (");
			for (ISort s : e.argSorts()) { s.accept(this); append(" "); }
			append(") ");
			e.resultSort().accept(this);
		});
	}

	@Override
	public Void visit(ICommand.Ideclare_sort e) throws IVisitor.VisitorException {
		return printCommand(e, () -> {
			e.sortSymbol().accept(this);
			append(" ");
			e.arity().accept(this);
		});
	}

	@Override
	public Void visit(ICommand.Ideclare_sort_parameter e) throws IVisitor.VisitorException {
		return printCommand(e, () -> e.sortSymbol().accept(this));
	}

	@Override
	public Void visit(ICommand.Idefine_const e) throws IVisitor.VisitorException {
		return printCommand(e, () -> {
			e.symbol().accept(this);
			append(" ");
			e.resultSort().accept(this);
			append(" ");
			e.expression().accept(this);
		});
	}

	@Override
	public Void visit(ICommand.Idefine_fun e) throws IVisitor.VisitorException {
		return printCommand(e, () -> {
			e.symbol().accept(this);
			append(" (");
			for (IExpr.IDeclaration d : e.parameters()) d.accept(this);
			append(") ");
			e.resultSort().accept(this);
			append(" ");
			e.expression().accept(this);
		});
	}

	@Override
	public Void visit(ICommand.Idefine_fun_rec e) throws IVisitor.VisitorException {
		return printCommand(e, () -> {
			e.symbol().accept(this);
			append(" (");
			for (IExpr.IDeclaration d : e.parameters()) d.accept(this);
			append(") ");
			e.resultSort().accept(this);
			append(" ");
			e.expression().accept(this);
		});
	}

	@Override
	public Void visit(ICommand.Idefine_funs_rec e) throws IVisitor.VisitorException {
		return printCommand(e, () -> {
			append("(");
			for (IExpr.IFunctionDeclaration d : e.declarations()) { d.accept(this); append(" "); }
			append(") (");
			for (IExpr body : e.bodies()) { body.accept(this); append(" "); }
			append(")");
		});
	}

	@Override
	public Void visit(ICommand.Idefine_sort e) throws IVisitor.VisitorException {
		return printCommand(e, () -> {
			e.sortSymbol().accept(this);
			append(" (");
			for (ISort.IParameter d : e.parameters()) { d.accept(this); append(" "); }
			append(") ");
			e.expression().accept(this);
		});
	}

	@Override
	public Void visit(ICommand.Iecho e) throws IVisitor.VisitorException {
		return printCommand(e, () -> e.arg().accept(this));
	}

	@Override
	public Void visit(ICommand.Iexit e) throws IVisitor.VisitorException {
		return printCommand(e);
	}

	@Override
	public Void visit(ICommand.Iget_assertions e) throws IVisitor.VisitorException {
		return printCommand(e);
	}

	@Override
	public Void visit(ICommand.Iget_assignment e) throws IVisitor.VisitorException {
		return printCommand(e);
	}

	@Override
	public Void visit(ICommand.Iget_info e) throws IVisitor.VisitorException {
		return printCommand(e, () -> e.infoflag().accept(this));
	}

	@Override
	public Void visit(ICommand.Iget_model e) throws IVisitor.VisitorException {
		return printCommand(e);
	}

	@Override
	public Void visit(ICommand.Iget_option e) throws IVisitor.VisitorException {
		return printCommand(e, () -> e.option().accept(this));
	}

	@Override
	public Void visit(ICommand.Iget_proof e) throws IVisitor.VisitorException {
		return printCommand(e);
	}

	@Override
	public Void visit(ICommand.Iget_unsat_assumptions e) throws IVisitor.VisitorException {
		return printCommand(e);
	}

	@Override
	public Void visit(ICommand.Iget_unsat_core e) throws IVisitor.VisitorException {
		return printCommand(e);
	}

	@Override
	public Void visit(ICommand.Iget_value e) throws IVisitor.VisitorException {
		return printCommand(e, () -> {
			append("(");
			for (IExpr x : e.exprs()) { append(" "); x.accept(this); }
			append(")");
		});
	}

	@Override
	public Void visit(ICommand.Ipop e) throws IVisitor.VisitorException {
		return printCommand(e, () -> e.number().accept(this));
	}

	@Override
	public Void visit(ICommand.Ipush e) throws IVisitor.VisitorException {
		return printCommand(e, () -> e.number().accept(this));
	}

	@Override
	public Void visit(ICommand.Ireset e) throws IVisitor.VisitorException {
		return printCommand(e);
	}

	@Override
	public Void visit(ICommand.Ireset_assertions e) throws IVisitor.VisitorException {
		return printCommand(e);
	}

	@Override
	public Void visit(ICommand.Iset_info e) throws IVisitor.VisitorException {
		return printCommand(e, () -> {
			e.infoflag().accept(this);
			append(" ");
			e.value().accept(this);
		});
	}

	@Override
	public Void visit(ICommand.Iset_logic e) throws IVisitor.VisitorException {
		return printCommand(e, () -> e.logic().accept(this));
	}

	@Override
	public Void visit(ICommand.Iset_option e) throws IVisitor.VisitorException {
		return printCommand(e, () -> {
			e.option().accept(this);
			append(" ");
			e.value().accept(this);
		});
	}

	@Override
	public Void visit(IFamily s) throws IVisitor.VisitorException {
		// A sort family is referenced by its bare identifier; the full
		// (declare-sort name arity) syntax is printed separately by
		// visit(ICommand.Ideclare_sort), never by way of an IFamily.
		s.identifier().accept(this);
		return null;
	}

	@Override
	public Void visit(IAbbreviation s) throws IVisitor.VisitorException {
		append("(");
		s.identifier().accept(this);
		append(" (");
		boolean first = true;
		for (ISort.IParameter p: s.parameters()) {
			if (!first) append(" ");
			p.accept(this);
			first = false;
		}
		append(") ");
		s.sortExpression().accept(this);
		append(")");
		return null;
	}

	@Override
	public Void visit(IApplication s) throws IVisitor.VisitorException {
		if (s.parameters().size() == 0) {
			s.family().accept(this);
		} else {
			append("(");
			s.family().accept(this);
			for (ISort ss: s.parameters()) {
				append(" ");
				ss.accept(this);
			}
			append(")");
		}
		return null;
	}

	@Override
	public Void visit(IFcnSort s) throws IVisitor.VisitorException {
		// Not real SMT-LIB syntax (function sorts aren't first-class there) - an
		// internal diagnostic form only; see e.g. Utils.java's symbol-table error messages.
		append("(");
		boolean first = true;
		for (ISort ss: s.argSorts()) {
			if (!first) append(" ");
			ss.accept(this);
			first = false;
		}
		append(") -> ");
		s.resultSort().accept(this);
		return null;
	}

	@Override
	public Void visit(IParameter s) throws IVisitor.VisitorException {
		s.symbol().accept(this);
		return null;
	}

	@Override
	public Void visit(ILogic s) throws IVisitor.VisitorException {
		append("(logic ");
		s.logicName().accept(this);
		for (IAttribute<?> attr: s.attributes().values()) {
			append(" ");
			attr.accept(this);
		}
		append(")");
		return null;
	}

	@Override
	public Void visit(ITheory s) throws IVisitor.VisitorException {
		append("(theory ");
		s.theoryName().accept(this);
		for (IAttribute<?> attr: s.attributes().values()) {
			append(" ");
			attr.accept(this);
		}
		append(")");
		return null;
	}

	@Override
	public Void visit(IResponse e) throws IVisitor.VisitorException {
		// Since S-expressions are not in the abstract syntax, they
		// end up here
		if (e instanceof ISexpr.ISeq) {
			return visit((ISexpr.ISeq)e);
		} else if (e instanceof ISexpr.IToken<?>) {
			return visit((ISexpr.IToken<?>)e);
		} else {
			throw new VisitorException("Undelegated IResponse in Printer for " + e.getClass(),null);
		}
	}

	/** Utility function to create an exception using the message from the first argument and the
	 * position from the second, if it is IPosable.
	 */
	public IVisitor.VisitorException exc(Exception ex, Object possiblePos) {
		return new IVisitor.VisitorException(ex,
			possiblePos instanceof IPos.IPosable ? ((IPos.IPosable)possiblePos).pos() : null);
	}

	/** Utility function to print error messages in this printer's format */
	public String error(String message) {
		return "(error " + smtConfig.utils.quote(message) + ")";
	}

	@Override
	public Void visit(IResponse.IError e) throws IVisitor.VisitorException {
		append(error(e.errorMsg()));
		return null;
	}

	@Override
	public Void visit(IAssertionsResponse e) throws IVisitor.VisitorException {
		append("(");
		append(eol);
		for (IExpr n : e.assertions()) {
			n.accept(this);
			append(eol);
		}
		append(")");
		return null;
	}

	@Override
	public Void visit(IAssignmentResponse e) throws IVisitor.VisitorException {
		append("(");
		for (IResponse.IPair<ISymbol,Boolean> p : e.assignments()) {
			append("(");
			p.first().accept(this);
			append(" ");
			append(p.second().toString()); // FIXME - change when we do not use Boolean
			append(")");
		}
		append(")");
		return null;
	}

	@Override
	public Void visit(IProofResponse e) throws IVisitor.VisitorException {
		// TODO when proofs are defined
		append("PROOF");
		return null;
	}

	@Override
	public Void visit(IValueResponse e) throws IVisitor.VisitorException {
		append("(");
		for (IResponse.IPair<IExpr,IExpr> p : e.values()) {
			append("(");
			p.first().accept(this);
			append(" ");
			p.second().accept(this);
			append(")");
		}
		append(")");
		return null;
	}

	@Override
	public Void visit(IUnsatCoreResponse e) throws IVisitor.VisitorException {
		append("(");
		for (ISymbol n : e.names()) {
			n.accept(this);
			append(" ");
		}
		append(")");
		return null;
	}

	@Override
	public Void visit(IResponse.IUnsatAssumptionsResponse e) throws IVisitor.VisitorException {
		append("(");
		for (ISymbol n : e.names()) {
			n.accept(this);
			append(" ");
		}
		append(")");
		return null;
	}

	@Override
	public Void visit(IAttributeList e) throws IVisitor.VisitorException {
		append("(");
		for (IAttribute<?> n : e.attributes()) {
			n.accept(this);
			append(" ");
		}
		append(")");
		return null;
	}

	public Void visit(ISexpr.IToken<?> e) throws IVisitor.VisitorException {
		append(String.valueOf(e.value()));
		return null;
	}

	/*@Nullable*/
	public Void visit(ISexpr.ISeq e) throws IVisitor.VisitorException {
		append("(");
		for (ISexpr expr: e.sexprs()) {
			append(" ");
			expr.accept(this);
		}
		append(" )");
		return null;
	}

    @Override
    public Void visit(ISort.IDatatype e) throws VisitorException {
        if (e.symbols() != null) {
            append("( par (");
            for (IExpr.ISymbol s : e.symbols()) { s.accept(this); append(" "); }
            append(") (");
            for (IExpr.IConstructor c : e.constructors()) { c.accept(this); append(" "); }
            append(") )");
        } else {
            append("(");
            for (IExpr.IConstructor c : e.constructors()) { c.accept(this); append(" "); }
            append(")");
        }
        return null;
    }
}
