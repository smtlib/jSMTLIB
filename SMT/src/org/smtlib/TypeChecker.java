/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib;
// FIXME- NEEDS REVIEW; use an interface?

import java.math.BigInteger;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.smtlib.IExpr.*;
import org.smtlib.ISort.*;
import org.smtlib.SMT.Configuration.SMTLIB;
import org.smtlib.impl.SMTExpr;
import org.smtlib.sexpr.ISexpr;
import org.smtlib.sexpr.ISexpr.ISeq;

/** This class is a visitor that type-checks a formula */
public class TypeChecker extends IVisitor.NullVisitor</*@Nullable*/ ISort> {

	/** Compilation of errors */
	public List<IResponse> result = new LinkedList<IResponse>();

	/** A reference to the current symbol table */
	private SymbolTable symTable;

	/** A reference to the current configuration */
	private SMT.Configuration smtConfig;
	
	private ISymbol isClosed = null;

	/** Constructs a formula typechecker from the current symbol table; sorts computed while
	 * checking are recorded directly on each IExpr node via IExpr.setSort(). */
	public TypeChecker(SymbolTable symTable) {
		this.symTable = symTable;
		this.smtConfig = symTable.smtConfig;
	}
	
	/** Utility method for recording an error */
	protected void error(String msg, IPos pos) {
		result.add(smtConfig.responseFactory.error(msg,pos));
	}
	
	/** Utility method for printing an expression, using the default printer */
	protected String pr(IExpr e) {
		return smtConfig.defaultPrinter.toString(e);
	}

	/** Utility method for printing a sort, using the default printer */
	protected String pr(ISort e) {
		return smtConfig.defaultPrinter.toString(e);
	}

	public static List<IResponse> checkSortAbbreviation(SymbolTable symTable, IIdentifier id, List<ISort.IParameter> params, ISort expr) {
		TypeChecker f = new TypeChecker(symTable); // FIXME - we should use a factory
		symTable.push();
		boolean errors = false;
		try {
            symTable.logicInUse.checkSortDeclaration(id,params,expr);
			if (params != null) for (ISort.IParameter p : params) {
				boolean b = symTable.addSortParameter(p.symbol(), false);
				if (!b) {
					f.error("Duplicate sort parameters: " + p.symbol(),p.pos());
					errors = true;
				}
			}
			if (!errors && expr != null) expr.accept(f);
		} catch (IVisitor.VisitorException e) {
			f.error("Error while checking sort abbreviation: " + e.getMessage(),id.pos());
		} catch (Exception e) {
			f.error("INTERNAL ERROR: Exception while checking sort abbreviation: " + e.getMessage(),expr.pos());
		} finally {
			symTable.pop();
		}
		return f.result;
	}
	
	public static List<IResponse> checkFcn(SymbolTable symTable, IIdentifier id, List<ISort> sorts, ISort result, IPos pos) {
		TypeChecker f = new TypeChecker(symTable);
		try {
			for (ISort p : sorts) {
				p.accept(f);
			}
			ISort newresult = result.accept(f);
			try {
				symTable.logicInUse.checkFcnDeclaration(id,sorts,newresult,null);
			} catch (IVisitor.VisitorException e) {
				f.error(e.getMessage(), e.pos());
			}
		} catch (IVisitor.VisitorException e) {
			f.error("INTERNAL ERROR: Exception while checking sort abbreviation: " + e.getMessage(), pos);
		} catch (Exception e) {
			f.error("INTERNAL ERROR: Exception while checking sort abbreviation: " + e.getMessage(), null);
		}
		return f.result;
		
	}

	public static List<IResponse> checkFcn(SymbolTable symTable, IIdentifier id, List<IDeclaration> params, ISort result, IExpr expr) {
		TypeChecker f = new TypeChecker(symTable);
		symTable.push();
		try {
			for (IDeclaration p : params) {
				if (p.sort().accept(f) != null) {
					ISort.IFcnSort fs = symTable.smtConfig.sortFactory.createFcnSort(new ISort[0],p.sort());
					SymbolTable.Entry entry = new SymbolTable.Entry(p.parameter(),fs,null,null);
					symTable.add(entry, false, true);
				}
			}
			if (f.result.isEmpty()) {
				ISort res = result.accept(f);
				if (res != null) {
					res = expr.accept(f);
				}
				if (res != null && !res.equals(result)) {
					f.error("Declared sort of the result does not match the sort of the expression: "
							+ symTable.smtConfig.defaultPrinter.toString(result) + " vs. " 
							+ symTable.smtConfig.defaultPrinter.toString(res),result.pos());
				}
			}
			try {
				List<ISort> sorts = new LinkedList<ISort>(); 
				for (IDeclaration p : params) sorts.add(p.sort());
				symTable.logicInUse.checkFcnDeclaration(id,sorts,result,expr);
				symTable.logicInUse.validExpression(expr);
			} catch (IVisitor.VisitorException e) {
				f.error(e.getMessage(), e.pos());
			}
		} catch (IVisitor.VisitorException e) {
			f.error("INTERNAL ERROR: Exception while checking sort abbreviation: " + e.getMessage(),expr.pos());
		} catch (Exception e) {
			f.error("INTERNAL ERROR: Exception while checking sort abbreviation: " + e.getMessage(),expr.pos());
		} finally {
			symTable.pop();
		}
		return f.result;
		
	}

	/** Checks that parameter sorts and result sort are well-formed, without examining a body expression.
	 * Sort errors should be caught before the function symbol is added to the symbol table so that
	 * a failed define-fun-rec does not leave a symbol with a malformed type. */
	static List<IResponse> checkSorts(SymbolTable symTable,
			List<IDeclaration> params, ISort resultSort) {
		TypeChecker f = new TypeChecker(symTable);
		try {
			for (IDeclaration p : params) {
				if (p.sort().accept(f) == null) break;
			}
			if (f.result.isEmpty()) {
				resultSort.accept(f);
			}
		} catch (IVisitor.VisitorException e) {
			f.error("INTERNAL ERROR: Exception while checking sorts: " + e.getMessage(), e.pos());
		}
		return f.result;
	}

	/** Type-checks a define-fun-rec command: verifies the symbol is new, validates sorts,
	 * pre-adds the function to the symbol table so the body may call it recursively,
	 * then checks the body expression.  On success the entry's definition is set.
	 * Delegates to checkFcnsRec as the N=1 case (a singleton declaration group). */
	public static List<IResponse> checkFcnRec(SymbolTable symTable,
			boolean global, ISymbol id, List<IDeclaration> params, ISort result, IExpr expr) {
		return checkFcnsRec(symTable, global,
				Collections.singletonList(new SMTExpr.FunctionDeclaration(id, params, result)),
				Collections.singletonList(expr));
	}

	/** Type-checks a define-funs-rec command: for each declaration verifies the symbol is new and
	 * sorts are valid, pre-adds all functions to the symbol table for mutual recursion, then
	 * checks each body expression.  On success all entries' definitions are set. */
	public static List<IResponse> checkFcnsRec(SymbolTable symTable,
			boolean global, List<IFunctionDeclaration> decls, List<IExpr> bodies) {
		List<SymbolTable.Entry> entries = new LinkedList<>();
		for (IFunctionDeclaration decl : decls) {
			if (symTable.lookup(decl.parameters().size(), decl.symbol()) != null) {
				List<IResponse> errors = new LinkedList<>();
				errors.add(symTable.smtConfig.responseFactory.error(
						"Symbol " + symTable.smtConfig.defaultPrinter.toString(decl.symbol()) + " is already defined",
						decl.symbol().pos()));
				return errors;
			}
			List<IResponse> sortErrors = checkSorts(symTable, decl.parameters(), decl.sort());
			if (!sortErrors.isEmpty()) return sortErrors;
			ISort[] argSorts = new ISort[decl.parameters().size()];
			for (int i = 0; i < decl.parameters().size(); i++) argSorts[i] = decl.parameters().get(i).sort();
			ISort.IFcnSort fcnSort = symTable.smtConfig.sortFactory.createFcnSort(argSorts, decl.sort());
			SymbolTable.Entry entry = new SymbolTable.Entry(decl.symbol(), fcnSort, null, null);
			symTable.add(entry, global);
			entries.add(entry);
		}
		for (int i = 0; i < decls.size(); i++) {
			IFunctionDeclaration decl = decls.get(i);
			List<IResponse> bodyErrors = checkFcn(symTable, decl.symbol(),
					decl.parameters(), decl.sort(), bodies.get(i));
			if (!bodyErrors.isEmpty()) return bodyErrors;
			entries.get(i).definition = bodies.get(i);
		}
		return new LinkedList<>();
	}

	/** The main entry point for type-checking an IExpr (expected to be a Bool)*/
	public static List<IResponse> check(SymbolTable symTable, IExpr expr) {
		TypeChecker f = new TypeChecker(symTable);
		try {
			ISort topsort = expr.accept(f);
			if (topsort != null && !topsort.isBool()) {
				f.error("Expected an expression with Bool sort, not " + topsort, expr.pos());
			}
			try {
				symTable.logicInUse.validExpression(expr);
			} catch (IVisitor.VisitorException e) {
				f.error(e.getMessage(), e.pos());
			}
		} catch (IVisitor.VisitorException e) {
			f.error("Visitor Exception: " + e.getMessage(), e.pos());
		} catch (Exception e) {
			f.error("INTERNAL ERROR: Exception while checking sort abbreviation: " + e.getMessage(),expr.pos());
		}
		return f.result;
	}

	/** The main entry point for type-checking an assert expression (expected to be a Bool); unlike
	 * {@link #check(SymbolTable,IExpr)}, this checks the expression within a pushed scope that is
	 * merged into the enclosing scope on success (or popped on error). */
	public static List<IResponse> checkAssertion(SymbolTable symTable, IExpr expr) {
		TypeChecker f = new TypeChecker(symTable);
		symTable.push();
		try {
			ISort topsort = expr.accept(f);
			if (topsort != null && !topsort.isBool()) {
				f.error("Expected an expression with Bool sort, not " + topsort, expr.pos());
			}
			try {
				symTable.logicInUse.validExpression(expr);
			} catch (IVisitor.VisitorException e) {
				f.error(e.getMessage(), e.pos());
			}
			if (f.result.isEmpty()) symTable.merge();
		} catch (IVisitor.VisitorException e) {
			f.error("Visitor Exception: " + e.getMessage(), e.pos());
		} catch (Exception e) {
			f.error("INTERNAL ERROR: Exception while checking sort abbreviation: " + e.getMessage(),expr.pos());
		} finally {
			if (!f.result.isEmpty()) symTable.pop();
		}
		return f.result;
	}

	public /*@Nullable*/ ISort save(/*@NonNull*/IExpr e, /*@Nullable*/ISort s) {
		e.setSort(s);
		return s;
	}

	/** Walks the given expression subtree, nulling out the sort recorded on each node
	 * (e.g. because it is leaving the live assertion set, on pop or reset-assertions). */
	public static void clearSorts(IExpr expr) throws IVisitor.VisitorException {
		expr.accept(new IVisitor.TreeVisitor<Void>() {
			@Override public Void visit(IAttributedExpr e) throws IVisitor.VisitorException { e.setSort(null); return super.visit(e); }
			@Override public Void visit(IBinaryLiteral e) throws IVisitor.VisitorException { e.setSort(null); return super.visit(e); }
			@Override public Void visit(IDecimal e) throws IVisitor.VisitorException { e.setSort(null); return super.visit(e); }
			@Override public Void visit(IExists e) throws IVisitor.VisitorException { e.setSort(null); return super.visit(e); }
			@Override public Void visit(IFcnExpr e) throws IVisitor.VisitorException { e.setSort(null); return super.visit(e); }
			@Override public Void visit(IForall e) throws IVisitor.VisitorException { e.setSort(null); return super.visit(e); }
			@Override public Void visit(IHexLiteral e) throws IVisitor.VisitorException { e.setSort(null); return super.visit(e); }
			@Override public Void visit(ILet e) throws IVisitor.VisitorException { e.setSort(null); return super.visit(e); }
			@Override public Void visit(INumeral e) throws IVisitor.VisitorException { e.setSort(null); return super.visit(e); }
			@Override public Void visit(IParameterizedIdentifier e) throws IVisitor.VisitorException { e.setSort(null); return super.visit(e); }
			@Override public Void visit(IAsIdentifier e) throws IVisitor.VisitorException { e.setSort(null); return super.visit(e); }
			@Override public Void visit(IStringLiteral e) throws IVisitor.VisitorException { e.setSort(null); return super.visit(e); }
			@Override public Void visit(ISymbol e) throws IVisitor.VisitorException { e.setSort(null); return super.visit(e); }
			@Override public Void visit(IError e) throws IVisitor.VisitorException { e.setSort(null); return super.visit(e); }
			@Override public Void visit(IMatch e) throws IVisitor.VisitorException { e.setSort(null); return super.visit(e); }
		});
	}


	@Override
	public /*@Nullable*/ ISort visit(INumeral e) {
		IFcnSort sort = symTable.lookup(0,smtConfig.exprFactory.symbol("NUMERAL"));
		if (sort == null) error("No sort specified for numeral",e.pos());
		return save(e,sort == null ? null : sort.resultSort());
	}

	@Override
	public /*@Nullable*/ ISort visit(IFcnExpr e) throws IVisitor.VisitorException {
		// Type check all the arguments
		boolean anyErrors = false;
		List<ISort> argSorts = new LinkedList<ISort>();
		java.util.Iterator<IExpr> iter = e.args().iterator();
		while (iter.hasNext()) {
			IExpr sx = iter.next();
			ISort argSort = sx.accept(this);
			anyErrors = anyErrors || (argSort == null);
			if (argSort != null) argSorts.add(argSort); 
		}
		if (anyErrors) return null;

		// Now lookup the head in the context of these arguments
		IQualifiedIdentifier qhead = e.head();
		IIdentifier head;
		ISort resultSort = null;
		if (qhead instanceof IAsIdentifier) {
			resultSort = qhead.accept(this);
			if (resultSort == null) return null;
			head = ((IAsIdentifier)qhead).head();
		} else {
			head = (IIdentifier)qhead;
		}
		boolean bvperhaps = symTable.bitVectorTheorySet && head.headSymbol().value().startsWith("bv");
		boolean fpperhaps = symTable.floatingPointTheorySet && (Utils.FP.equals(head) || head.headSymbol().value().startsWith("fp."));
		String name = head.toString();
		// =, distinct, ite, store, select, and @ are all declared as par_fun_symbol_decl
		// entries (Core.smt2, ArraysEx.smt2, HO-Core.smt2) and used to be hardcoded here
		// because Utils.loadFuns() used to skip "par" declarations entirely -- now that it
		// doesn't, and SymbolTable.lookup() can unify against them (including the
		// :chainable/:pairwise/:left-assoc n-ary sugar =, distinct, and @ each need), they
		// fall through to the general lookup below like any other declared function, with
		// SymbolTable.lookup()'s `reason` output giving as specific a message as these
		// hardcoded branches used to (see its doc comment).
		boolean useext = true;
		if (bvperhaps) {
			if (head.equals(Utils.BVNOT) || head.equals(Utils.BVNEG)) {
				if (argSorts.size() != 1) {
					error(" The " + name + " function should have one argument",head.pos());
					return null;
				}
				ISort s = argSorts.get(0);
				if (!isBitVec(s)) {
					error("The argument must have a BitVec sort, not " + smtConfig.defaultPrinter.toString(s),e.args().get(0).pos());
					return null;
				}
				return save(e,s);
				
			} else if (head.equals(Utils.BVAND) || head.equals(Utils.BVOR)
					|| head.equals(Utils.BVADD) || head.equals(Utils.BVMUL)) {
				// bvand, bvor, bvadd, bvmul are :left-assoc per FixedSizeBitVectors.smt2's
				// :funs-description prose (informal text, not parsed :funs data -- see
				// Utils.loadFuns -- so unlike +/-/*'s generic SymbolTable.lookup() left-assoc
				// handling, these schematic BV ops need the check spelled out here): SMT-LIB
				// Sec. 3.7.2 says (f t1 t2 t3 ...) with n > 2 is sugar for (f (f t1 t2) t3) ...,
				// which for these ops just means every argument must share the same BitVec sort.
				if (argSorts.size() < 2) {
					error(" The " + name + " function should have at least two arguments",head.pos());
					return null;
				}
				ISort s = argSorts.get(0);
				if (!isBitVec(s)) {
					error("The argument must have a BitVec sort, not " + pr(s),e.args().get(0).pos());
					return null;
				}
				for (int i = 1; i < argSorts.size(); i++) {
					ISort ss = argSorts.get(i);
					if (!isBitVec(ss)) {
						error("The argument must have a BitVec sort, not " + pr(ss),e.args().get(i).pos());
						return null;
					}
					if (!s.equals(ss)) {
						error("The sorts must match: " + pr(s) + " vs. " + pr(ss),e.pos());
						return null;
					}
				}
				return save(e,s);
			} else if (head.equals(Utils.BVUDIV) || head.equals(Utils.BVUREM)
					|| head.equals(Utils.BVSHL) || head.equals(Utils.BVLSHR) ||
					(useext && (head.equals(Utils.BVNAND) || head.equals(Utils.BVNOR) || head.equals(Utils.BVXOR) || head.equals(Utils.BVXNOR)
							|| head.equals(Utils.BVSUB) || head.equals(Utils.BVSDIV) || head.equals(Utils.BVSREM) || head.equals(Utils.BVSMOD)
							|| head.equals(Utils.BVASHR) || head.equals(Utils.BVCOMP)
					))
					) {
				if (argSorts.size() != 2) {
					error(" The " + name + " function should have two arguments",head.pos());
					return null;
				}
				ISort s = argSorts.get(0);
				if (!isBitVec(s)) {
					error("The argument must have a BitVec sort, not " + pr(s),e.args().get(0).pos());
					return null;
				}
				ISort ss = argSorts.get(1);
				if (!isBitVec(ss)) {
					error("The argument must have a BitVec sort, not " + pr(ss),e.args().get(1).pos());
					return null;
				}
				if (!s.equals(ss)) {
					error("The sorts must match: " + pr(s) + " vs. " + pr(ss),e.pos());
					return null;
				}
				if (head.equals(Utils.BVCOMP)) {
					s = makeBitVec(1);
					return save(e,s);
				}
				return save(e,s);
			} else if (head.equals(Utils.BVULT) || (useext && (head.equals(Utils.BVULE) || head.equals(Utils.BVUGT) || head.equals(Utils.BVUGE)
					|| head.equals(Utils.BVSLT) || head.equals(Utils.BVSLE) || head.equals(Utils.BVSGT) || head.equals(Utils.BVSGE)
					|| head.equals(Utils.BVUADDO) || head.equals(Utils.BVSADDO) || head.equals(Utils.BVUMULO) || head.equals(Utils.BVSMULO)
					)
					)) {
				if (argSorts.size() != 2) {
					error(" The " + name + " function should have two arguments",head.pos());
					return null;
				}
				ISort s = argSorts.get(0);
				if (!isBitVec(s)) {
					error("The argument must have a BitVec sort, not " + pr(s),e.args().get(0).pos());
					return null;
				}
				ISort ss = argSorts.get(1);
				if (!isBitVec(ss)) {
					error("The argument must have a BitVec sort, not " + pr(ss),e.args().get(1).pos());
					return null;
				}
				if (!s.equals(ss)) {
					error("The sorts must match: " + pr(s) + " vs. " + pr(ss),e.pos());
					return null;
				}
				ISort b = smtConfig.sortFactory.Bool(); // FIXME - get something from the symbol table?
				b.accept(this);
				return save(e,b);
			} else if (useext && head.equals(Utils.BVNEGO)) {
				if (argSorts.size() != 1) {
					error(" The " + name + " function should have one argument",head.pos());
					return null;
				}
				ISort s = argSorts.get(0);
				if (!isBitVec(s)) {
					error("The argument must have a BitVec sort, not " + pr(s),e.args().get(0).pos());
					return null;
				}
				ISort b = smtConfig.sortFactory.Bool();
				b.accept(this);
				return save(e,b);
			}

		}
		if (fpperhaps) {
			if (head.equals(Utils.FP)) {
				// (fp sign exponent significand): sign is (_ BitVec 1), exponent is
				// (_ BitVec eb), significand is (_ BitVec sb-1) (the hidden bit is not
				// represented) -- (eb,sb) is computed from the argument widths, the same
				// direction concat computes its result width from its arguments, rather
				// than requiring the target sort to already be known.
				if (argSorts.size() != 3) {
					error(" The fp function should have three arguments",head.pos());
					return null;
				}
				ISort sign = argSorts.get(0), exp = argSorts.get(1), sig = argSorts.get(2);
				if (!isBitVec(sign) || bitvecSize(sign) != 1) {
					error("The first argument of fp must have sort (_ BitVec 1), not " + pr(sign),e.args().get(0).pos());
					return null;
				}
				if (!isBitVec(exp)) {
					error("The second argument of fp must have a BitVec sort, not " + pr(exp),e.args().get(1).pos());
					return null;
				}
				if (!isBitVec(sig)) {
					error("The third argument of fp must have a BitVec sort, not " + pr(sig),e.args().get(2).pos());
					return null;
				}
				// eb>1/sb>1 validity is checked and reported by makeFloatingPoint -> lookupSort,
				// the same way makeBitVec relies on lookupSort to catch length==0
				ISort s = makeFloatingPoint(bitvecSize(exp), bitvecSize(sig)+1);
				return save(e,s);
			} else if (head.equals(Utils.FP_SQRT) || head.equals(Utils.FP_ROUND_TO_INTEGRAL)) {
				if (argSorts.size() != 2) {
					error(" The " + name + " function should have two arguments",head.pos());
					return null;
				}
				if (!isRoundingMode(argSorts.get(0))) {
					error("The first argument of " + name + " must have RoundingMode sort, not " + pr(argSorts.get(0)),e.args().get(0).pos());
					return null;
				}
				ISort s = argSorts.get(1);
				if (!isFloatingPoint(s)) {
					error("The second argument of " + name + " must have a FloatingPoint sort, not " + pr(s),e.args().get(1).pos());
					return null;
				}
				return save(e,s);
			} else if (head.equals(Utils.FP_ADD) || head.equals(Utils.FP_SUB)
					|| head.equals(Utils.FP_MUL) || head.equals(Utils.FP_DIV)) {
				if (argSorts.size() != 3) {
					error(" The " + name + " function should have three arguments",head.pos());
					return null;
				}
				if (!isRoundingMode(argSorts.get(0))) {
					error("The first argument of " + name + " must have RoundingMode sort, not " + pr(argSorts.get(0)),e.args().get(0).pos());
					return null;
				}
				ISort s = argSorts.get(1);
				if (!isFloatingPoint(s)) {
					error("The second argument of " + name + " must have a FloatingPoint sort, not " + pr(s),e.args().get(1).pos());
					return null;
				}
				ISort ss = argSorts.get(2);
				if (!isFloatingPoint(ss) || !s.equals(ss)) {
					error("The sorts must match: " + pr(s) + " vs. " + pr(ss),e.pos());
					return null;
				}
				return save(e,s);
			} else if (head.equals(Utils.FP_FMA)) {
				if (argSorts.size() != 4) {
					error(" The fp.fma function should have four arguments",head.pos());
					return null;
				}
				if (!isRoundingMode(argSorts.get(0))) {
					error("The first argument of fp.fma must have RoundingMode sort, not " + pr(argSorts.get(0)),e.args().get(0).pos());
					return null;
				}
				ISort s = argSorts.get(1);
				if (!isFloatingPoint(s)) {
					error("The second argument of fp.fma must have a FloatingPoint sort, not " + pr(s),e.args().get(1).pos());
					return null;
				}
				for (int i = 2; i <= 3; i++) {
					ISort ss = argSorts.get(i);
					if (!isFloatingPoint(ss) || !s.equals(ss)) {
						error("The sorts must match: " + pr(s) + " vs. " + pr(ss),e.pos());
						return null;
					}
				}
				return save(e,s);
			} else if (head.equals(Utils.FP_ABS) || head.equals(Utils.FP_NEG)) {
				if (argSorts.size() != 1) {
					error(" The " + name + " function should have one argument",head.pos());
					return null;
				}
				ISort s = argSorts.get(0);
				if (!isFloatingPoint(s)) {
					error("The argument of " + name + " must have a FloatingPoint sort, not " + pr(s),e.args().get(0).pos());
					return null;
				}
				return save(e,s);
			} else if (head.equals(Utils.FP_REM) || head.equals(Utils.FP_MIN) || head.equals(Utils.FP_MAX)) {
				// fp.rem/fp.min/fp.max are fixed 2-arg -- FloatingPoint.smt2's :funs-description
				// does not list :left-assoc/:chainable for these (unlike fp.leq & co. below), so
				// this exact-2 check is deliberate, not the bvand-style oversight fixed elsewhere
				// in this file for bvand/bvor/bvadd/bvmul.
				if (argSorts.size() != 2) {
					error(" The " + name + " function should have two arguments",head.pos());
					return null;
				}
				ISort s = argSorts.get(0);
				if (!isFloatingPoint(s)) {
					error("The first argument of " + name + " must have a FloatingPoint sort, not " + pr(s),e.args().get(0).pos());
					return null;
				}
				ISort ss = argSorts.get(1);
				if (!isFloatingPoint(ss) || !s.equals(ss)) {
					error("The sorts must match: " + pr(s) + " vs. " + pr(ss),e.pos());
					return null;
				}
				return save(e,s);
			} else if (head.equals(Utils.FP_LEQ) || head.equals(Utils.FP_LT)
					|| head.equals(Utils.FP_GEQ) || head.equals(Utils.FP_GT) || head.equals(Utils.FP_EQ)) {
				// fp.leq/fp.lt/fp.geq/fp.gt/fp.eq are :chainable per FloatingPoint.smt2's
				// :funs-description prose -- SMT-LIB Sec. 3.7.2: (f t1 t2 ... tn) with n > 2
				// means (and (f t1 t2) (f t2 t3) ... (f t(n-1) tn)), which for this theory just
				// means every argument must share the same FloatingPoint sort. This is genuinely
				// n-ary from the start (a loop over argSorts.size() >= 2), mirroring how
				// bvand/bvor/bvadd/bvmul were FIXED to be n-ary elsewhere in this file -- they
				// were originally hardcoded to exactly 2 args despite being :left-assoc, which
				// is exactly the mistake to not repeat here.
				if (argSorts.size() < 2) {
					error(" The " + name + " function should have at least two arguments",head.pos());
					return null;
				}
				ISort s = argSorts.get(0);
				if (!isFloatingPoint(s)) {
					error("The argument must have a FloatingPoint sort, not " + pr(s),e.args().get(0).pos());
					return null;
				}
				for (int i = 1; i < argSorts.size(); i++) {
					ISort ss = argSorts.get(i);
					if (!isFloatingPoint(ss)) {
						error("The argument must have a FloatingPoint sort, not " + pr(ss),e.args().get(i).pos());
						return null;
					}
					if (!s.equals(ss)) {
						error("The sorts must match: " + pr(s) + " vs. " + pr(ss),e.pos());
						return null;
					}
				}
				ISort b = smtConfig.sortFactory.Bool();
				b.accept(this);
				return save(e,b);
			} else if (head.equals(Utils.FP_IS_NORMAL) || head.equals(Utils.FP_IS_SUBNORMAL)
					|| head.equals(Utils.FP_IS_ZERO) || head.equals(Utils.FP_IS_INFINITE)
					|| head.equals(Utils.FP_IS_NAN) || head.equals(Utils.FP_IS_NEGATIVE)
					|| head.equals(Utils.FP_IS_POSITIVE)) {
				if (argSorts.size() != 1) {
					error(" The " + name + " function should have one argument",head.pos());
					return null;
				}
				if (!isFloatingPoint(argSorts.get(0))) {
					error("The argument of " + name + " must have a FloatingPoint sort, not " + pr(argSorts.get(0)),e.args().get(0).pos());
					return null;
				}
				ISort b = smtConfig.sortFactory.Bool();
				b.accept(this);
				return save(e,b);
			} else if (head.equals(Utils.FP_TO_REAL)) {
				if (argSorts.size() != 1) {
					error(" The fp.to_real function should have one argument",head.pos());
					return null;
				}
				if (!isFloatingPoint(argSorts.get(0))) {
					error("The argument of fp.to_real must have a FloatingPoint sort, not " + pr(argSorts.get(0)),e.args().get(0).pos());
					return null;
				}
				return save(e,makeReal());
			}
		}
		if (symTable.bitVectorTheorySet && head.equals(Utils.CONCAT)) {
			if (argSorts.size() != 2) {
				error(" The " + name + " function should have two arguments",head.pos());
				return null;
			}
			ISort s = argSorts.get(0);
			if (!isBitVec(s)) {
				error("The argument must have a BitVec sort, not " + pr(s),e.args().get(0).pos());
				return null;
			}
			ISort ss = argSorts.get(1);
			if (!isBitVec(ss)) {
				error("The argument must have a BitVec sort, not " + pr(ss),e.args().get(1).pos());
				return null;
			}
			s = makeBitVec(bitvecSize(s)+bitvecSize(ss));
			return save(e,s);
		}
		if (symTable.bitVectorTheorySet && symTable.realsIntsTheorySet &&
				(head.equals(Utils.UBV_TO_INT) || head.equals(Utils.SBV_TO_INT))) {
			if (argSorts.size() != 1) {
				error(" The " + name + " function should have one argument",head.pos());
				return null;
			}
			ISort s = argSorts.get(0);
			if (!isBitVec(s)) {
				error("The argument must have a BitVec sort, not " + pr(s),e.args().get(0).pos());
				return null;
			}
			ISort i = makeInt();
			if (i == null) {
				error("No Int sort available for " + name,head.pos());
				return null;
			}
			return save(e,i);
		}
		ISymbol pheadSymbol = null;
		if (head instanceof IParameterizedIdentifier) pheadSymbol = ((IParameterizedIdentifier)head).headSymbol();
		if (symTable.bitVectorTheorySet &&
				head instanceof IParameterizedIdentifier &&
				Utils.EXTRACT.equals(pheadSymbol)) {
			if (argSorts.size() != 1) {
				error(" The " + name + " function should have one argument",head.pos());
				return null;
			}
			ISort s = argSorts.get(0);
			if (!isBitVec(s)) {
				error("The argument must have a BitVec sort, not " + pr(s),e.args().get(0).pos());
				return null;
			}
			IParameterizedIdentifier pid = (IParameterizedIdentifier)head;
			if (!checkNumeralIndices(pid, 2, "Expected exactly two numerals in an extract identifier")) return null;
			int end = ((INumeral) pid.indices().get(0)).intValue();
			int start = ((INumeral) pid.indices().get(1)).intValue();
			if (end < start) {
				error("The end index is less than the starting index",pid.indices().get(1).pos());
				return null;
			}
			int len = bitvecSize(s);
			if (end >= len) {
				error("The end index must be less than the length of the argument sort: " + end + " vs. " + len, pid.indices().get(1).pos());
				return null;
			}
			s = makeBitVec(end-start+1);
			return save(e,s);

		}
		if (symTable.bitVectorTheorySet && symTable.realsIntsTheorySet &&
				head instanceof IParameterizedIdentifier &&
				Utils.INT_TO_BV.equals(pheadSymbol)) {
			if (argSorts.size() != 1) {
				error(" The " + name + " function should have one argument",head.pos());
				return null;
			}
			ISort s = argSorts.get(0);
			if (!isIntSort(s)) {
				error("The argument must have Int sort, not " + pr(s),e.args().get(0).pos());
				return null;
			}
			IParameterizedIdentifier pid = (IParameterizedIdentifier)head;
			if (!checkNumeralIndices(pid, 1, "Expected exactly one numeral in an int_to_bv identifier")) return null;
			int val = ((INumeral) pid.indices().get(0)).intValue();
			if (val <= 0) {
				error("The numeral must be greater than 0 in int_to_bv",pid.indices().get(0).pos());
				return null;
			}
			s = makeBitVec(val);
			return save(e,s);

		}
		if (useext && symTable.bitVectorTheorySet &&
				head instanceof IParameterizedIdentifier &&
				Utils.REPEAT.equals(pheadSymbol)) {
			if (argSorts.size() != 1) {
				error(" The " + name + " function should have one argument",head.pos());
				return null;
			}
			ISort s = argSorts.get(0);
			if (!isBitVec(s)) {
				error("The argument must have a BitVec sort, not " + pr(s),e.args().get(0).pos());
				return null;
			}
			IParameterizedIdentifier pid = (IParameterizedIdentifier)head;
			if (!checkNumeralIndices(pid, 1, "Expected exactly one numeral in a repeat identifier")) return null;
			int val = ((INumeral) pid.indices().get(0)).intValue();
			if (val == 0) {
				error("The numeral may not be 0 in a repeat",pid.indices().get(0).pos());
				return null;
			}
			s = makeBitVec(val*bitvecSize(s));
			return save(e,s);

		}
		
		if (useext && symTable.bitVectorTheorySet &&
				head instanceof IParameterizedIdentifier &&
				(Utils.ZERO_EXTEND.equals(pheadSymbol) || Utils.SIGN_EXTEND.equals(pheadSymbol)
				)) {
			if (argSorts.size() != 1) {
				error(" The " + name + " function should have one argument",head.pos());
				return null;
			}
			ISort s = argSorts.get(0);
			if (!isBitVec(s)) {
				error("The argument must have a BitVec sort, not " + pr(s),e.args().get(0).pos());
				return null;
			}
			IParameterizedIdentifier pid = (IParameterizedIdentifier)head;
			if (!checkNumeralIndices(pid, 1, "Expected exactly one numeral in a repeat identifier")) return null;
			int val = ((INumeral) pid.indices().get(0)).intValue();
			s = makeBitVec(val+bitvecSize(s));
			return save(e,s);

		}
		if (useext && symTable.bitVectorTheorySet &&
				head instanceof IParameterizedIdentifier &&
				(Utils.ROTATE_LEFT.equals(pheadSymbol) || Utils.ROTATE_RIGHT.equals(pheadSymbol)
				)) {
			if (argSorts.size() != 1) {
				error(" The " + name + " function should have one argument",head.pos());
				return null;
			}
			ISort s = argSorts.get(0);
			if (!isBitVec(s)) {
				error("The argument must have a BitVec sort, not " + pr(s),e.args().get(0).pos());
				return null;
			}
			IParameterizedIdentifier pid = (IParameterizedIdentifier)head;
			if (!checkNumeralIndices(pid, 1, "Expected exactly one numeral in a repeat identifier")) return null;
			return save(e,s);

		}
		if (symTable.floatingPointTheorySet && symTable.bitVectorTheorySet &&
				head instanceof IParameterizedIdentifier &&
				(Utils.FP_TO_UBV.equals(pheadSymbol) || Utils.FP_TO_SBV.equals(pheadSymbol))) {
			if (argSorts.size() != 2) {
				error(" The " + name + " function should have two arguments",head.pos());
				return null;
			}
			if (!isRoundingMode(argSorts.get(0))) {
				error("The first argument of " + name + " must have RoundingMode sort, not " + pr(argSorts.get(0)),e.args().get(0).pos());
				return null;
			}
			if (!isFloatingPoint(argSorts.get(1))) {
				error("The second argument of " + name + " must have a FloatingPoint sort, not " + pr(argSorts.get(1)),e.args().get(1).pos());
				return null;
			}
			IParameterizedIdentifier pid = (IParameterizedIdentifier)head;
			if (!checkNumeralIndices(pid, 1, "Expected exactly one numeral in a " + pheadSymbol + " identifier")) return null;
			int m = ((INumeral) pid.indices().get(0)).intValue();
			if (m <= 0) {
				error("The numeral must be greater than 0",pid.indices().get(0).pos());
				return null;
			}
			ISort s = makeBitVec(m);
			return save(e,s);
		}
		if (symTable.floatingPointTheorySet && symTable.bitVectorTheorySet &&
				head instanceof IParameterizedIdentifier &&
				Utils.TO_FP_UNSIGNED.equals(pheadSymbol)) {
			IParameterizedIdentifier pid = (IParameterizedIdentifier)head;
			if (!checkNumeralIndices(pid, 2, "Expected exactly two numerals (eb sb) in a to_fp_unsigned identifier")) return null;
			ISort target = makeFloatingPoint(((INumeral) pid.indices().get(0)).intValue(), ((INumeral) pid.indices().get(1)).intValue());
			if (argSorts.size() != 2) {
				error(" The to_fp_unsigned function should have two arguments",head.pos());
				return null;
			}
			if (!isRoundingMode(argSorts.get(0))) {
				error("The first argument of to_fp_unsigned must have RoundingMode sort, not " + pr(argSorts.get(0)),e.args().get(0).pos());
				return null;
			}
			if (!isBitVec(argSorts.get(1))) {
				error("The second argument of to_fp_unsigned must have a BitVec sort, not " + pr(argSorts.get(1)),e.args().get(1).pos());
				return null;
			}
			return save(e,target);
		}
		if (symTable.floatingPointTheorySet &&
				head instanceof IParameterizedIdentifier &&
				Utils.TO_FP.equals(pheadSymbol)) {
			// (_ to_fp eb sb) has four overloads sharing one indexed head name, disambiguated
			// by argument count then (for count 2) the second argument's sort: (a) 1 BitVec arg
			// of width eb+sb -- reinterpret bits; (b) RoundingMode + FloatingPoint -- convert
			// between precisions (source (mb,nb) need not match target); (c) RoundingMode +
			// Real -- convert from Real; (d) RoundingMode + BitVec -- convert from a signed
			// 2's-complement integer. Argument count alone separates (a) from (b)-(d); the
			// second argument's sort alone separates (b)/(c)/(d) -- no case needs more than
			// "count, then one sort."
			IParameterizedIdentifier pid = (IParameterizedIdentifier)head;
			if (!checkNumeralIndices(pid, 2, "Expected exactly two numerals (eb sb) in a to_fp identifier")) return null;
			int eb = ((INumeral) pid.indices().get(0)).intValue();
			int sb = ((INumeral) pid.indices().get(1)).intValue();
			ISort target = makeFloatingPoint(eb, sb); // also re-validates eb>1, sb>1 via lookupSort
			if (argSorts.size() == 1) {
				ISort s = argSorts.get(0);
				if (!symTable.bitVectorTheorySet || !isBitVec(s)) {
					error("The argument of to_fp/1 must have a BitVec sort, not " + pr(s),e.args().get(0).pos());
					return null;
				}
				if (bitvecSize(s) != eb + sb) {
					error("The argument's BitVec width must be " + (eb+sb) + ", not " + bitvecSize(s),e.args().get(0).pos());
					return null;
				}
				return save(e,target);
			} else if (argSorts.size() == 2) {
				if (!isRoundingMode(argSorts.get(0))) {
					error("The first argument of to_fp/2 must have RoundingMode sort, not " + pr(argSorts.get(0)),e.args().get(0).pos());
					return null;
				}
				ISort second = argSorts.get(1);
				if (isFloatingPoint(second)) {
					return save(e,target);
				} else if (isRealSort(second)) {
					return save(e,target);
				} else if (symTable.bitVectorTheorySet && isBitVec(second)) {
					return save(e,target);
				} else {
					error("The second argument of to_fp/2 must have FloatingPoint, Real, or BitVec sort, not " + pr(second),e.args().get(1).pos());
					return null;
				}
			} else {
				error(" The to_fp function should have one or two arguments",head.pos());
				return null;
			}
		}

		StringBuilder reason = new StringBuilder();
		ISort matchedResultSort = symTable.lookup(head,argSorts,resultSort,reason);
		if (matchedResultSort == null && symTable.realsIntsTheorySet) {
			ISort realSort = null;
			for (ISort sort: argSorts) {
				if (isRealSort(sort)) realSort = sort;
			}
			if (realSort != null) {
				List<ISort> newargs = new LinkedList<ISort>();
				for (ISort sort: argSorts) {
					if (isIntSort(sort)) {
						newargs.add(realSort);
					} else {
						newargs.add(sort);
					}
				}
				reason.setLength(0);
				matchedResultSort = symTable.lookup(head,newargs,resultSort,reason);
			}
		}
		if (matchedResultSort == null) {
			String msg;
			if (reason.length() > 0) {
				// A candidate (or candidates) exist for this name but none matched these
				// argument sorts -- symTable.lookup() already explains why, in more detail
				// than a generic "unknown symbol" message could.
				msg = reason.toString();
			} else {
				msg = "Unknown predicate symbol " + name + " with argument types";
				for (ISort s: argSorts) {
					msg = msg + " " + smtConfig.defaultPrinter.toString(s);
				}
			}
			error(msg,e.pos());
			return null;
		} else {
			return save(e,matchedResultSort);
		}
	}
	
	private boolean isBitVec(ISort s) {
		// expand() first: a user-defined alias for a BitVec sort (e.g.
		// (define-sort Word32 () (_ BitVec 32))) has family() literally "Word32", not a
		// parameterized "BitVec" identifier, until expanded through its IAbbreviation
		// definition -- without this, isBitVec (and so every bv* operator) would wrongly
		// reject an otherwise-legitimate Word32-sorted argument. Same fix, same reasoning,
		// as isFloatingPoint() below (added for Float16/32/64/128); isRealSort()/isIntSort()
		// just below have the identical unfixed gap for a hypothetical Real/Int alias, but
		// nothing currently exercises one, so they are left as they were.
		s = s.expand();
		if (!(s instanceof ISort.IApplication)) return false;
		ISort.IApplication se = (ISort.IApplication)s;
		if (!(se.family() instanceof IParameterizedIdentifier)) return false;
		IParameterizedIdentifier pid = (IParameterizedIdentifier)se.family();
		return Utils.BITVEC_SYM.equals(pid.headSymbol());
	}

	// Real/Int sort checks are only needed here, for the Int-to-Real coercion rule
	// in visit(IFcnExpr) - kept local rather than promoted to a general ISort
	// capability like isBool(), since nothing else in the codebase needs them.
	private static final ISymbol REAL_SYM = new SMTExpr.Symbol("Real".intern());
	private static final ISymbol INT_SYM = new SMTExpr.Symbol("Int".intern());

	private boolean isRealSort(ISort s) {
		return (s instanceof ISort.IApplication) && REAL_SYM.equals(((ISort.IApplication)s).family().headSymbol());
	}

	private boolean isIntSort(ISort s) {
		return (s instanceof ISort.IApplication) && INT_SYM.equals(((ISort.IApplication)s).family().headSymbol());
	}

	private int bitvecSize(ISort s) {
		s = s.expand(); // see isBitVec() above
		if (!(s instanceof ISort.IApplication)) return -1;
		ISort.IApplication se = (ISort.IApplication)s;
		if (!(se.family() instanceof IParameterizedIdentifier)) return -1;
		IParameterizedIdentifier pid = (IParameterizedIdentifier)se.family();
		if (pid.indices().size() != 1 || !(pid.indices().get(0) instanceof INumeral)) return -1;
		return ((INumeral) pid.indices().get(0)).intValue();
	}
	
	private ISort makeBitVec(int length) throws IVisitor.VisitorException {
		List<IExpr.IIndex> nums = new LinkedList<IExpr.IIndex>();
		nums.add(smtConfig.exprFactory.numeral(length));
		// FIXME - use a pre-constructed symbol for BitVec when it does not have a position?
		IIdentifier id = smtConfig.exprFactory.id(smtConfig.exprFactory.symbol(Utils.BITVEC),nums);
		ISort s = smtConfig.sortFactory.createSortExpression(id, new ISort[0]);
		s.accept(this);
		return s;
	}

	private boolean isFloatingPoint(ISort s) {
		// expand() first: a Float16/Float32/Float64/Float128-sorted value (see SymbolTable.
		// lookupSort's alias handling) has family() literally "Float32" etc, not a
		// parameterized "FloatingPoint" identifier, until expanded through its
		// IAbbreviation definition -- without this, isFloatingPoint (and so every fp.*
		// operator) would wrongly reject an otherwise-legitimate Float32-sorted argument.
		s = s.expand();
		if (!(s instanceof ISort.IApplication)) return false;
		ISort.IApplication se = (ISort.IApplication)s;
		if (!(se.family() instanceof IParameterizedIdentifier)) return false;
		IParameterizedIdentifier pid = (IParameterizedIdentifier)se.family();
		return Utils.FLOATINGPOINT_SYM.equals(pid.headSymbol());
	}

	private boolean isRoundingMode(ISort s) {
		s = s.expand(); // see isBitVec() above
		return (s instanceof ISort.IApplication) && Utils.ROUNDINGMODE_SYM.equals(((ISort.IApplication)s).family().headSymbol());
	}

	private ISort makeFloatingPoint(int eb, int sb) throws IVisitor.VisitorException {
		List<IExpr.IIndex> nums = new LinkedList<IExpr.IIndex>();
		nums.add(smtConfig.exprFactory.numeral(eb));
		nums.add(smtConfig.exprFactory.numeral(sb));
		IIdentifier id = smtConfig.exprFactory.id(smtConfig.exprFactory.symbol(Utils.FLOATINGPOINT),nums);
		ISort s = smtConfig.sortFactory.createSortExpression(id, new ISort[0]);
		s.accept(this);
		return s;
	}

	/** Returns the Real sort, as registered generically by whichever theory declares it
	 * (Reals/Reals_Ints's own :sorts, or FloatingPoint's own :sorts -- FloatingPoint.smt2
	 * declares Real itself so this does not require Reals_Ints to also be loaded). */
	private ISort makeReal() throws IVisitor.VisitorException {
		ISort s = smtConfig.sortFactory.createSortExpression(smtConfig.exprFactory.symbol("Real"), new ISort[0]);
		s.accept(this);
		return s;
	}

	/** Returns the Int sort as installed by the active theories (Ints/Reals_Ints), or
	 * null if none is installed -- mirrors how numeral literals are sorted (visit(INumeral)). */
	private /*@Nullable*/ ISort makeInt() {
		IFcnSort sort = symTable.lookup(0,smtConfig.exprFactory.symbol("NUMERAL"));
		return sort == null ? null : sort.resultSort();
	}

	@Override
	/*@checkers.igj.quals.ReadOnly*/
	public /*@Nullable*/ ISort visit(ISymbol e) {
		IFcnSort sort = null;
		String value = e.value();
		if (Utils.WILDCARD.equals(value)) {
			error("The _ wildcard may only appear in match patterns", e.pos());
			return null;
		}
		if (Utils.TRUE.equals(e) || Utils.FALSE.equals(e)) {
			return save(e,symTable.smtConfig.sortFactory.Bool());
		} else {
			Variable v = currentScope.get(e);
			if (v != null) {
				if (isClosed == null && v.expression == null) isClosed = e; // FIXME - need to check if v.expression is closed or not
				return save(e,v.sort);
			}
			if ((sort=symTable.lookup(0,e))==null) {
				result.add(smtConfig.responseFactory.error("Unknown constant symbol " + value, e.pos()));
				return null;
			} else {
				return save(e,sort.resultSort());
			}
		}
	}


	@Override
	public /*@Nullable*/ISort visit(IDecimal e) {
		IFcnSort sort = symTable.lookup(0,smtConfig.exprFactory.symbol("DECIMAL")); // FIXME - don't recreate this every time it is used
		if (sort == null) result.add(smtConfig.responseFactory.error("No sort specified for decimal literal",e.pos()));
		return save(e,sort == null ? null : sort.resultSort());
	}

	@Override
	public /*@Nullable*/ISort visit(IBinaryLiteral e) throws IVisitor.VisitorException {
		if (!symTable.bitVectorTheorySet) result.add(smtConfig.responseFactory.error("No sort specified for a binary literal",e.pos()));
		ISort s = makeBitVec(e.length());
		s.accept(this);
		return save(e,s);
	}

	@Override
	public /*@Nullable*/ ISort visit(IHexLiteral e) throws IVisitor.VisitorException {
		if (!symTable.bitVectorTheorySet) result.add(smtConfig.responseFactory.error("No sort specified for a hex literal",e.pos()));
		List<IExpr.IIndex> nums = new LinkedList<IExpr.IIndex>();
		nums.add(smtConfig.exprFactory.numeral(e.length()*4));
		IIdentifier id = smtConfig.exprFactory.id(smtConfig.exprFactory.symbol(Utils.BITVEC),nums);
		ISort s = smtConfig.sortFactory.createSortExpression(id, new ISort[0]);
		s.accept(this);
		return save(e,s);
	}

	@Override
	public /*@Nullable*/ ISort visit(IStringLiteral e) {
		IFcnSort sort = symTable.lookup(0,smtConfig.exprFactory.symbol("STRING")); // FIXME - don't recreate this everytime it is used
		if (sort == null) result.add(smtConfig.responseFactory.error("No sort specified for string-literal",e.pos()));
		return save(e,sort == null ? null : sort.resultSort());
	}

	@Override
	public /*@Nullable*/ ISort visit(IKeyword e) {
		// Should never be called
		result.add(smtConfig.responseFactory.error("INTERNAL ERROR: Did not expect to be type-checking a keyword",e.pos()));
		return null;
	}

	@Override
	public /*@Nullable*/ ISort visit(IError e) {
		return null;
	}

	/** Checks that pid has exactly {@code count} indices and all are INumeral.
	 *  Records {@code errorMsg} at pid.pos() and returns false if not. */
	private boolean checkNumeralIndices(IExpr.IParameterizedIdentifier pid, int count, String errorMsg) {
		if (pid.indices().size() != count) { error(errorMsg, pid.pos()); return false; }
		for (IIndex idx : pid.indices()) {
			if (!(idx instanceof INumeral)) { error(errorMsg, pid.pos()); return false; }
		}
		return true;
	}

	private void requireVersionForSymbolIndex(IExpr.IParameterizedIdentifier pid) {
		if (!smtConfig.atLeastVersion(SMT.Configuration.SMTLIB.V25)) {
			for (IIndex idx : pid.indices()) {
				if (idx instanceof ISymbol) {
					error("Symbol indices in indexed identifiers require SMT-LIB V2.5 or later", idx.pos());
					return;
				}
			}
		}
	}

	@Override
	public /*@Nullable*/ ISort visit(IParameterizedIdentifier e) throws IVisitor.VisitorException {
		requireVersionForSymbolIndex(e);
		IFcnSort sort = null;
		boolean useext = true;
		String pname = e.headSymbol().value();
		if (useext && symTable.bitVectorTheorySet &&
				(pname.matches("bv(0|[1-9][0-9]*)") // TODO - allow leading zeros?
				)) {
			if (!checkNumeralIndices(e, 1, "Expected exactly one numeral in a bv identifier")) return null;
			int size = ((INumeral) e.indices().get(0)).intValue();
			BigInteger value = new BigInteger(pname.substring(2));
			if (value.bitLength() > size) {
				error("The value of the bitvector constant is too large for the given size (" + value.bitLength() + " vs. " + size + " bits)",e.pos());
				return null;
			}
			ISort s = makeBitVec(size);
			return save(e,s);
		}
		if (useext && symTable.floatingPointTheorySet &&
				(Utils.FP_POS_INF.equals(e.headSymbol()) || Utils.FP_NEG_INF.equals(e.headSymbol())
				|| Utils.FP_POS_ZERO.equals(e.headSymbol()) || Utils.FP_NEG_ZERO.equals(e.headSymbol())
				|| Utils.FP_NAN.equals(e.headSymbol()))) {
			if (!checkNumeralIndices(e, 2, "Expected exactly two numerals (eb sb) in a " + pname + " identifier")) return null;
			int eb = ((INumeral) e.indices().get(0)).intValue();
			int sb = ((INumeral) e.indices().get(1)).intValue();
			ISort s = makeFloatingPoint(eb, sb);
			return save(e,s);
		}

		if ((sort=symTable.lookup(0,e))==null) {
			result.add(smtConfig.responseFactory.error("No sort known for identifier: " + smtConfig.defaultPrinter.toString(e),e.pos()));
			return null;
		} else {
			return save(e,sort.resultSort());
		}
	}

	@Override
	public /*@Nullable*/ ISort visit(IAsIdentifier e) throws IVisitor.VisitorException {
		// Check the sort
		ISort s = e.qualifier().accept(this);
		// We do the rest of the checking in the parent (IFcnExpr)
		return s;
	}

	@Override
	public /*@Nullable*/ ISort visit(IAttributedExpr e) throws IVisitor.VisitorException {
		ISymbol savedIsClosed = isClosed;
		isClosed = null;
		boolean errors = false;
		ISort resultSort = null;
		try {
			resultSort = save(e,e.expr().accept(this));
			for (IAttribute<?> a: e.attributes()) {
				String name = a.keyword().value();
				if (name.equals(":named")) { // FIXME - use a canonical representation
					IAttributeValue v = a.attrValue();
					if (!(v instanceof ISymbol)) {
						result.add(smtConfig.responseFactory.error("Expected a symbol after :named",v==null?a.keyword().pos():v.pos()));
						errors = true;
					}
					ISort.IFcnSort fcnSort = smtConfig.sortFactory.createFcnSort(new ISort[0],resultSort);
					SymbolTable.Entry entry = new SymbolTable.Entry((ISymbol)v,fcnSort,null,null);
					if (!symTable.add(entry, false, false)) { 
						result.add(smtConfig.responseFactory.error("Symbol " + v.toString() + " is already defined",v.pos())); // FIXME - encode name
						errors = true;
					}
					if (isClosed != null) {
						result.add(smtConfig.responseFactory.error("The expression being named is not closed - this symbol is a variable: " + smtConfig.defaultPrinter.toString(isClosed),isClosed.pos()));
						errors = true;
					}
				} else if (name.equals(":pattern")) {
					IAttributeValue v = a.attrValue();
					if (!(v instanceof ISeq)) {
						result.add(smtConfig.responseFactory.error("Expected a sequence after :pattern",v==null?a.keyword().pos():v.pos()));
						errors = true;
					} else {
						for (ISexpr ee: ((ISeq)v).sexprs()) {
							IExpr ex = convert(ee);
							ex.accept(this);
						}
					}
				}
			}
		} finally {
			isClosed = isClosed == null ? savedIsClosed : isClosed;
		}
		if (errors) return null;
		return resultSort;
	}
	
	public IExpr convert(ISexpr s) { // FIXME - use a factory? do typechecking here?
		if (s instanceof ISexpr.ISeq) {
			Iterator<ISexpr> sexprs = ((ISeq)s).sexprs().iterator();
			ISexpr first = sexprs.next();
			List<IExpr> args = new LinkedList<IExpr>();
			while (sexprs.hasNext()) {
				IExpr arg = convert(sexprs.next());
				args.add(arg);
			}
			ISymbol id = (ISymbol)first;
			return new SMTExpr.FcnExpr(id,args);
		} else if (s instanceof ISymbol) {
			return (ISymbol)s;
		} else {
			throw new RuntimeException();
		}
	}

	protected Map<ISymbol,Variable> currentScope = new HashMap<ISymbol,Variable>();
	protected List<Map<ISymbol,Variable>> parameters = new LinkedList<Map<ISymbol,Variable>>();

	@Override
	public /*@Nullable*/ ISort visit(IForall e) throws IVisitor.VisitorException {
		Map<ISymbol,Variable> saved = new HashMap<ISymbol,Variable>();
		saved.putAll(currentScope);
		parameters.add(0,saved);
		boolean errors = false;
		Set<ISymbol> seen = new HashSet<>();
		for (IExpr.IDeclaration decl : e.parameters()) {
			if (!seen.add(decl.parameter())) {
				error("Parameter list has a duplicate name: " + pr(decl.parameter()), decl.parameter().pos());
				errors = true;
			}
			ISort res = decl.sort().accept(this);
			if (res == null) errors = true;
			else currentScope.put(decl.parameter(),new Variable(decl.parameter(),decl.sort(),null));
		}
		try {
			if (errors) return null;
			ISort s = e.expr().accept(this);
			return save(e,s);
		} finally {
			currentScope = parameters.remove(0);
		}
	}

	@Override
	public /*@Nullable*/ ISort visit(IExists e) throws IVisitor.VisitorException {
		Map<ISymbol,Variable> saved = new HashMap<ISymbol,Variable>();
		saved.putAll(currentScope);
		parameters.add(0,saved);
		boolean errors = false;
		Set<ISymbol> seen = new HashSet<>();
		for (IExpr.IDeclaration decl : e.parameters()) {
			if (!seen.add(decl.parameter())) {
				error("Parameter list has a duplicate name: " + pr(decl.parameter()), decl.parameter().pos());
				errors = true;
			}
			ISort res = decl.sort().accept(this);
			if (res == null) errors = true;
			else currentScope.put(decl.parameter(),new Variable(decl.parameter(),decl.sort(),null));
		}
		try {
			if (errors) return null;
			ISort s = e.expr().accept(this);
			return save(e,s);
		} finally {
			currentScope = parameters.remove(0);
		}
	}

	@Override
	public /*@Nullable*/ ISort visit(ILet e) throws IVisitor.VisitorException {
		Map<ISymbol,Variable> newdecls = new HashMap<ISymbol,Variable>();
		Map<ISymbol,Variable> saved = new HashMap<ISymbol,Variable>();
		saved.putAll(currentScope);
		parameters.add(0,saved);
		try {
			boolean anyErrors = false;
			Set<ISymbol> seen = new HashSet<>();
			for (IExpr.IBinding decl : e.bindings()) {
				if (!seen.add(decl.parameter())) {
					error("Parameter list has a duplicate name: " + pr(decl.parameter()), decl.parameter().pos());
					anyErrors = true;
				}
				IExpr expr = decl.expr();
				ISort s = expr.accept(this);
				if (s == null) anyErrors = true;
				else {
					newdecls.put(decl.parameter(),new Variable(decl.parameter(),s,expr));
				}
			}
			if (anyErrors) return null;
			currentScope.putAll(newdecls);
			ISort s = e.expr().accept(this);
			return save(e,s);
		} finally {
			currentScope = parameters.remove(0);
		}
	}
	
	@Override
	public /*@Nullable*/ ISort visit(IExpr.IMatch e) throws IVisitor.VisitorException {
		if (!smtConfig.atLeastVersion(SMT.Configuration.SMTLIB.V26)) {
			error("The match expression requires SMT-LIB " + SMTLIB.V26 + " or later", e.pos());
			return null;
		}
		ISort scrutineeSort = e.expr().accept(this);
		if (scrutineeSort == null) return null;

		// The scrutinee must be of a declared datatype sort
		String scrutineeSortName = null;
		if (scrutineeSort instanceof ISort.IApplication) {
			IIdentifier fam = ((ISort.IApplication)scrutineeSort).family();
			scrutineeSortName = fam.toString();
		}
		List<ISymbol> allCtors = (scrutineeSortName != null)
				? symTable.datatypeConstructors.get(scrutineeSortName) : null;
		if (allCtors == null) {
			error("The scrutinee of a match expression must be of a datatype sort, but has sort "
					+ pr(scrutineeSort), e.expr().pos());
			return null;
		}

		if (e.cases().isEmpty()) {
			error("A match expression must have at least one case", e.pos());
			return null;
		}

		ISort resultSort = null;
		boolean anyErrors = false;
		boolean hasVariableOrWildcard = false;
		Set<String> coveredCtors = new HashSet<>();

		for (IExpr.IMatchCase mc : e.cases()) {
			Map<ISymbol,Variable> saved = new HashMap<ISymbol,Variable>();
			saved.putAll(currentScope);
			parameters.add(0, saved);
			try {
				IExpr.IPattern pat = mc.pattern();

				if (pat.params().isEmpty()) {
					if (Utils.WILDCARD.equals(pat.constructor().value())) {
						if (!smtConfig.atLeastVersion(SMTLIB.V27)) {
							error("The _ wildcard in match patterns requires SMT-LIB V2.7 or later", pat.constructor().pos());
							anyErrors = true;
						}
						hasVariableOrWildcard = true;
					} else {
						IFcnSort ctorSort = symTable.lookup(0, pat.constructor());
						if (ctorSort == null || !scrutineeSort.equals(ctorSort.resultSort())) {
							// Not a nullary constructor of this sort — treat as variable binding
							currentScope.put(pat.constructor(), new Variable(pat.constructor(), scrutineeSort, null));
							hasVariableOrWildcard = true;
						} else {
							coveredCtors.add(pat.constructor().value());
						}
					}
				} else {
					int arity = pat.params().size();
					IFcnSort ctorSort = symTable.lookup(arity, pat.constructor());
					if (ctorSort == null) {
						error("Unknown constructor: " + pat.constructor().value(), pat.constructor().pos());
						anyErrors = true;
					} else if (!scrutineeSort.equals(ctorSort.resultSort())) {
						error("Constructor " + pat.constructor().value() + " has result sort "
								+ pr(ctorSort.resultSort()) + " but scrutinee has sort " + pr(scrutineeSort),
								pat.constructor().pos());
						anyErrors = true;
					} else {
						coveredCtors.add(pat.constructor().value());
						ISort[] argSorts = ctorSort.argSorts();
						List<IExpr.ISymbol> params = pat.params();
						Set<String> patternVarsSeen = new HashSet<>();
						for (int i = 0; i < params.size(); i++) {
							if (Utils.WILDCARD.equals(params.get(i).value())) {
								if (!smtConfig.atLeastVersion(SMTLIB.V27)) {
									error("The _ wildcard in match patterns requires SMT-LIB V2.7 or later", params.get(i).pos());
									anyErrors = true;
								}
							} else {
								if (!patternVarsSeen.add(params.get(i).value())) {
									error("Duplicate variable in match pattern: " + params.get(i).value(), params.get(i).pos());
									anyErrors = true;
								} else {
									currentScope.put(params.get(i), new Variable(params.get(i), argSorts[i], null));
								}
							}
						}
					}
				}

				if (!anyErrors) {
					ISort bodySort = mc.body().accept(this);
					if (bodySort == null) {
						anyErrors = true;
					} else if (resultSort == null) {
						resultSort = bodySort;
					} else if (!resultSort.equals(bodySort)) {
						error("Match cases have incompatible sorts: " + pr(resultSort) + " vs. " + pr(bodySort),
								mc.body().pos());
						anyErrors = true;
					}
				}
			} finally {
				currentScope = parameters.remove(0);
			}
		}

		if (!anyErrors && !hasVariableOrWildcard) {
			List<String> missing = new java.util.ArrayList<>();
			for (ISymbol ctor : allCtors) {
				if (!coveredCtors.contains(ctor.value())) missing.add(ctor.value());
			}
			if (!missing.isEmpty()) {
				error("Non-exhaustive match: missing constructors: " + String.join(", ", missing), e.pos());
				anyErrors = true;
			}
		}

		if (anyErrors) return null;
		return save(e, resultSort);
	}

	@Override
	public /*@Nullable*/ ISort visit(ISort.IApplication s) throws IVisitor.VisitorException {
		IIdentifier f = s.family();
		if (f instanceof IExpr.IParameterizedIdentifier) {
			requireVersionForSymbolIndex((IExpr.IParameterizedIdentifier) f);
		}
		List<ISort> args = s.parameters();
		IDefinition def = symTable.lookupSort(f);
		if (def instanceof ISort.IErrorDefinition) {
			ISort.IErrorDefinition ed = (ISort.IErrorDefinition)def;
			error(ed.errorMessage(), ed.errorPos());
			return null;
		}
		s.definition(null);
		boolean errors = false;
		List<ISort> newargs = new LinkedList<ISort>();
		for (ISort ss : args) {
			ISort result = ss.accept(this);
			if (result == null) errors = true;
			else newargs.add(result);
		}
		if (def == null) {
			error("No such sort symbol declared: " + pr(f),f.pos());
			return null;
		}
		if (args.size() != def.intArity()) {
			// -> is declared :right-assoc in HO-Core.smt2 -- (-> t1 t2 t3) means
			// (-> t1 (-> t2 t3)) (SMT-LIB Sec. 3.7.2). This is a narrow, ->-specific
			// special case, not a general :right-assoc/:left-assoc mechanism: there is
			// currently no sort-level attribute data model at all to generalize from --
			// Utils.loadTheory()'s :sorts loop only ever reads a declaration's name and
			// arity, never any trailing attribute, and ISort.IDefinition/Sort.Family have
			// no attributes field the way SymbolTable.Entry does for functions. -> is also
			// the only sort declared with any attribute in any shipped theory file (checked
			// every :sorts declaration), so there is no present need to generalize this the
			// way @ needed a real fix (six theory functions needed par-polymorphism there,
			// not just one).
			if (Utils.ARROW.equals(f.headSymbol()) && def.intArity() == 2 && args.size() > 2 && !errors) {
				// newargs (not args) since these are the already-type-checked sorts, folded
				// right-to-left with the same Family.eval() the base 2-arg case already uses
				ISort result = newargs.get(newargs.size() - 1);
				for (int i = newargs.size() - 2; i >= 0; i--) {
					List<ISort> pair = new LinkedList<ISort>();
					pair.add(newargs.get(i));
					pair.add(result);
					result = def.eval(pair);
				}
				return result;
			}
			error("The sort symbol " + pr(f) + " expects " + def.intArity()
					+ " arguments, not " + args.size(), s.pos());
			return null;
		}
		if (errors) return null;
		s.definition(def);
		return def.eval(newargs);
	}
	
	@Override
	public /*@Nullable*/ ISort visit(ISort.IFamily s) throws IVisitor.VisitorException {
		error("INTERNAL ERROR - unexpected type-checking of a ISort.IFamily " + s, null);
		return null;
	}
	
	@Override
	public /*@Nullable*/ ISort visit(ISort.IParameter s) throws IVisitor.VisitorException {
		return s;
	}
	
	@Override
	public /*@Nullable*/ ISort visit(ISort.IAbbreviation s) throws IVisitor.VisitorException {
		error("INTERNAL ERROR - unexpected type-checking of a ISort.IAbbreviation " + s, null);// FIXME - check sort
		return null;
	}

	@Override
	public /*@Nullable*/ ISort visit(ISort.IFcnSort s) throws IVisitor.VisitorException {
		error("INTERNAL ERROR - unexpected type-checking of a ISort.IFcnSort " + s, s.pos());// FIXME - check sort
		return null;
	}
	
	private static void requireVersion(SMT.Configuration smtConfig, SMT.Configuration.SMTLIB minVersion,
			String cmdName, List<IResponse> errors) {
		if (!smtConfig.atLeastVersion(minVersion)) {
			errors.add(smtConfig.responseFactory.error(
				"The " + cmdName + " command requires SMT-LIB " + minVersion + " or later", null));
		}
	}

	/** Validates non-syntactic well-formedness of a command (user IDs, duplicate names, list sizes).
	 *  Returns a list of errors; an empty list means the command is well-formed. */
	public static List<IResponse> validate(SMT.Configuration smtConfig, ICommand cmd) {
		List<IResponse> errors = new LinkedList<>();
		if (cmd instanceof ICommand.Ideclare_const) {
			requireVersion(smtConfig, SMT.Configuration.SMTLIB.V25, "declare-const", errors);
			validateUserId(smtConfig, ((ICommand.Ideclare_const)cmd).symbol(), errors);
		} else if (cmd instanceof ICommand.Ideclare_fun) {
			validateUserId(smtConfig, ((ICommand.Ideclare_fun)cmd).symbol(), errors);
		} else if (cmd instanceof ICommand.Idefine_const) {
			requireVersion(smtConfig, SMT.Configuration.SMTLIB.V27, "define-const", errors);
			ICommand.Idefine_const c = (ICommand.Idefine_const)cmd;
			validateUserId(smtConfig, c.symbol(), errors);
		} else if (cmd instanceof ICommand.Idefine_fun) {
			ICommand.Idefine_fun c = (ICommand.Idefine_fun)cmd;
			validateUserId(smtConfig, c.symbol(), errors);
			if (errors.isEmpty()) validateUniqueDeclarations(smtConfig, c.parameters(), errors);
		} else if (cmd instanceof ICommand.Idefine_fun_rec) {
			requireVersion(smtConfig, SMT.Configuration.SMTLIB.V25, "define-fun-rec", errors);
			ICommand.Idefine_fun_rec c = (ICommand.Idefine_fun_rec)cmd;
			validateUserId(smtConfig, c.symbol(), errors);
			if (errors.isEmpty()) validateUniqueDeclarations(smtConfig, c.parameters(), errors);
		} else if (cmd instanceof ICommand.Idefine_funs_rec) {
			requireVersion(smtConfig, SMT.Configuration.SMTLIB.V25, "define-funs-rec", errors);
			ICommand.Idefine_funs_rec c = (ICommand.Idefine_funs_rec)cmd;
			if (c.declarations().size() != c.bodies().size())
				errors.add(smtConfig.responseFactory.error(
					"The number of function declarations (" + c.declarations().size() +
					") must equal the number of bodies (" + c.bodies().size() + ")", null));
		} else if (cmd instanceof ICommand.Ideclare_sort) {
			validateUserId(smtConfig, ((ICommand.Ideclare_sort)cmd).sortSymbol(), errors);
		} else if (cmd instanceof ICommand.Ideclare_sort_parameter) {
			requireVersion(smtConfig, SMT.Configuration.SMTLIB.V27, "declare-sort-parameter", errors);
			validateUserId(smtConfig, ((ICommand.Ideclare_sort_parameter)cmd).sortSymbol(), errors);
		} else if (cmd instanceof ICommand.Ideclare_datatype) {
			requireVersion(smtConfig, SMT.Configuration.SMTLIB.V26, "declare-datatype", errors);
			ICommand.Ideclare_datatype c1 = (ICommand.Ideclare_datatype)cmd;
			validateUserId(smtConfig, c1.sortDeclaration().symbol(), errors);
			if (errors.isEmpty())
				validateDatatypeGroup(smtConfig,
					Collections.singletonList(c1.sortDeclaration()),
					Collections.singletonList(c1.datatype()), errors);
		} else if (cmd instanceof ICommand.Ideclare_datatypes) {
			requireVersion(smtConfig, SMT.Configuration.SMTLIB.V26, "declare-datatypes", errors);
			ICommand.Ideclare_datatypes c = (ICommand.Ideclare_datatypes)cmd;
			if (c.sortDeclarations().isEmpty()) {
				errors.add(smtConfig.responseFactory.error(
					"Expected at least one sort declaration in declare-datatypes", null));
			} else if (c.sortDeclarations().size() != c.datatypes().size()) {
				errors.add(smtConfig.responseFactory.error(
					"Number of sort declarations (" + c.sortDeclarations().size() +
					") does not match number of datatype declarations (" + c.datatypes().size() + ")", null));
			} else {
				for (IExpr.ISortDeclaration sd : c.sortDeclarations()) {
					validateUserId(smtConfig, sd.symbol(), errors);
					if (!errors.isEmpty()) break;
				}
				if (errors.isEmpty())
					validateDatatypeGroup(smtConfig, c.sortDeclarations(), c.datatypes(), errors);
			}
		} else if (cmd instanceof ICommand.Idefine_sort) {
			ICommand.Idefine_sort c = (ICommand.Idefine_sort)cmd;
			validateUserId(smtConfig, c.sortSymbol(), errors);
			if (errors.isEmpty()) validateUniqueSortParams(smtConfig, c.parameters(), errors);
		} else if (cmd instanceof ICommand.Iecho) {
			requireVersion(smtConfig, SMT.Configuration.SMTLIB.V25, "echo", errors);
		} else if (cmd instanceof ICommand.Ireset) {
			requireVersion(smtConfig, SMT.Configuration.SMTLIB.V25, "reset", errors);
		} else if (cmd instanceof ICommand.Ireset_assertions) {
			requireVersion(smtConfig, SMT.Configuration.SMTLIB.V25, "reset-assertions", errors);
		} else if (cmd instanceof ICommand.Icheck_sat_assuming) {
			requireVersion(smtConfig, SMT.Configuration.SMTLIB.V25, "check-sat-assuming", errors);
			if (errors.isEmpty() && !smtConfig.atLeastVersion(SMT.Configuration.SMTLIB.V27)) {
				for (IExpr e : ((ICommand.Icheck_sat_assuming) cmd).terms()) {
					if (!isLiteralAssumption(e)) {
						errors.add(smtConfig.responseFactory.error(
							"Arguments to check-sat-assuming must be a symbol or (not symbol) in SMT-LIB V2.6 and earlier",
							e.pos()));
						break;
					}
				}
			}
		} else if (cmd instanceof ICommand.Iget_model) {
			requireVersion(smtConfig, SMT.Configuration.SMTLIB.V25, "get-model", errors);
		} else if (cmd instanceof ICommand.Iget_unsat_assumptions) {
			requireVersion(smtConfig, SMT.Configuration.SMTLIB.V25, "get-unsat-assumptions", errors);
		} else if (cmd instanceof ICommand.Iset_logic) {
			String logicName = ((ICommand.Iset_logic) cmd).logic().value();
			if ("ALL".equals(logicName) && !smtConfig.relax && !smtConfig.atLeastVersion(SMT.Configuration.SMTLIB.V25)) {
				errors.add(smtConfig.responseFactory.error(
					"The ALL logic requires SMT-LIB V2.5 or later", null));
			}
		}
		return errors;
	}

	private static boolean isLiteralAssumption(IExpr e) {
		if (e instanceof ISymbol) return true;
		if (e instanceof IFcnExpr) {
			IFcnExpr f = (IFcnExpr) e;
			return Utils.NOT.equals(f.head()) && f.args().size() == 1 && f.args().get(0) instanceof ISymbol;
		}
		return false;
	}

	private static void validateUserId(SMT.Configuration smtConfig, ISymbol id, List<IResponse> errors) {
		String v = id.value();
		if (v.isEmpty())
			errors.add(smtConfig.responseFactory.error("User-defined symbols may not be empty strings", id.pos()));
		else if (v.charAt(0) == '@' || v.charAt(0) == '.')
			errors.add(smtConfig.responseFactory.error("User-defined symbols may not begin with . or @", id.pos()));
	}

	private static void validateUniqueDeclarations(SMT.Configuration smtConfig,
			List<IExpr.IDeclaration> params, List<IResponse> errors) {
		Set<ISymbol> seen = new HashSet<>();
		for (IExpr.IDeclaration d : params) {
			if (!seen.add(d.parameter())) {
				errors.add(smtConfig.responseFactory.error(
					"A name is duplicated in the parameter list: " +
					smtConfig.defaultPrinter.toString(d.parameter()), d.parameter().pos()));
				return;
			}
		}
	}

	private static void validateUniqueSortParams(SMT.Configuration smtConfig,
			List<ISort.IParameter> params, List<IResponse> errors) {
		Set<String> seen = new HashSet<>();
		for (ISort.IParameter p : params) {
			if (!seen.add(p.symbol().value())) {
				errors.add(smtConfig.responseFactory.error(
					"A name is duplicated in the parameter list: " +
					smtConfig.defaultPrinter.toString(p.symbol()), p.pos()));
				return;
			}
		}
	}

	/** Validates a group of mutually declared datatypes against the SMT-LIB spec constraints. */
	private static void validateDatatypeGroup(SMT.Configuration smtConfig,
			List<IExpr.ISortDeclaration> sortDecls, List<ISort.IDatatype> datatypes,
			List<IResponse> errors) {
		Set<String> deltaNames = new LinkedHashSet<>();
		for (IExpr.ISortDeclaration sd : sortDecls) deltaNames.add(sd.symbol().value());

		for (int i = 0; i < sortDecls.size(); i++) {
			IExpr.ISortDeclaration sd = sortDecls.get(i);
			ISort.IDatatype dt = datatypes.get(i);
			String name = sd.symbol().value();

			// Arity-par consistency
			int k = sd.arity().intValue();
			List<IExpr.ISymbol> params = dt.symbols();
			int actualParams = (params == null) ? 0 : params.size();
			if (k != actualParams) {
				errors.add(smtConfig.responseFactory.error(
					"Arity " + k + " of sort " + name +
					" does not match the number of sort parameters (" + actualParams + ")",
					sd.symbol().pos()));
				return;
			}

			// Distinct sort parameters in par clause
			if (params != null) {
				Set<String> seen = new HashSet<>();
				for (IExpr.ISymbol p : params) {
					if (!seen.add(p.value())) {
						errors.add(smtConfig.responseFactory.error(
							"Duplicate sort parameter in datatype declaration: " + p.value(),
							p.pos()));
						return;
					}
				}
			}

			// At least one constructor
			if (dt.constructors().isEmpty()) {
				errors.add(smtConfig.responseFactory.error(
					"Datatype " + name + " must have at least one constructor",
					sd.symbol().pos()));
				return;
			}

			// No δi nested below top symbol in selector sorts
			for (IExpr.IConstructor ctor : dt.constructors()) {
				for (IExpr.ISelector sel : ctor.selectors()) {
					if (containsDeltaNestedBelowTop(sel.sort(), deltaNames)) {
						errors.add(smtConfig.responseFactory.error(
							"A recursive datatype must not appear nested inside another sort in a selector sort",
							sel.sort().pos()));
						return;
					}
				}
			}
		}

		// Well-foundedness: fixed-point algorithm
		Set<String> wellFounded = new HashSet<>();
		boolean changed;
		do {
			changed = false;
			for (int i = 0; i < sortDecls.size(); i++) {
				String name = sortDecls.get(i).symbol().value();
				if (wellFounded.contains(name)) continue;
				for (IExpr.IConstructor ctor : datatypes.get(i).constructors()) {
					boolean baseCase = true;
					for (IExpr.ISelector sel : ctor.selectors()) {
						if (anyDeltaNotInSet(sel.sort(), deltaNames, wellFounded)) {
							baseCase = false;
							break;
						}
					}
					if (baseCase) {
						wellFounded.add(name);
						changed = true;
						break; // found a base-case constructor; stop checking this datatype
					}
				}
			}
		} while (changed);

		for (String name : deltaNames) {
			if (!wellFounded.contains(name)) {
				errors.add(smtConfig.responseFactory.error(
					"Datatype " + name + " is not well-founded (no finite base case)", null));
			}
		}
	}

	/** Returns true if any δ in deltaNames appears as a non-head argument in sort. */
	private static boolean containsDeltaNestedBelowTop(ISort sort, Set<String> deltaNames) {
		if (!(sort instanceof ISort.IApplication)) return false;
		ISort.IApplication app = (ISort.IApplication) sort;
		for (ISort arg : app.parameters()) {
			if (anyDeltaInSort(arg, deltaNames)) return true;
		}
		return false;
	}

	/** Returns true if sort references any δ in deltaNames (including as head). */
	private static boolean anyDeltaInSort(ISort sort, Set<String> deltaNames) {
		if (!(sort instanceof ISort.IApplication)) return false;
		ISort.IApplication app = (ISort.IApplication) sort;
		if (deltaNames.contains(app.family().headSymbol().value())) return true;
		for (ISort arg : app.parameters()) {
			if (anyDeltaInSort(arg, deltaNames)) return true;
		}
		return false;
	}

	/** Returns true if sort references any δ ∈ deltaNames but ∉ wellFounded. */
	private static boolean anyDeltaNotInSet(ISort sort, Set<String> deltaNames, Set<String> wellFounded) {
		if (!(sort instanceof ISort.IApplication)) return false;
		ISort.IApplication app = (ISort.IApplication) sort;
		String head = app.family().headSymbol().value();
		if (deltaNames.contains(head) && !wellFounded.contains(head)) return true;
		for (ISort arg : app.parameters()) {
			if (anyDeltaNotInSet(arg, deltaNames, wellFounded)) return true;
		}
		return false;
	}

	/**
	 * Checks that constructor and selector names introduced by a datatype group are not
	 * already defined (neither in the symbol table nor duplicated within the group).
	 * Returns any errors found; empty list means all names are fresh.
	 */
	public static List<IResponse> validateDatatypeNames(SymbolTable symTable,
			SMT.Configuration smtConfig,
			List<IExpr.ISortDeclaration> sortDecls,
			List<ISort.IDatatype> datatypes) {
		List<IResponse> errors = new LinkedList<>();
		Set<String> newNames = new HashSet<>();
		for (int i = 0; i < sortDecls.size(); i++) {
			for (IExpr.IConstructor ctor : datatypes.get(i).constructors()) {
				String ctorName = ctor.symbol().value();
				if (!newNames.add(ctorName) || symTable.lookup(ctor.symbol()) != null) {
					errors.add(smtConfig.responseFactory.error(
						"Constructor " + ctorName + " is already defined", ctor.symbol().pos()));
					return errors;
				}
				for (IExpr.ISelector sel : ctor.selectors()) {
					String selName = sel.symbol().value();
					if (!newNames.add(selName) || symTable.lookup(sel.symbol()) != null) {
						errors.add(smtConfig.responseFactory.error(
							"Selector " + selName + " is already defined", sel.symbol().pos()));
						return errors;
					}
				}
			}
		}
		return errors;
	}

	public static class Variable {
		public ISymbol symbol;
		public ISort sort;
		public /*@Nullable*/IExpr expression;
		public Variable(ISymbol sym, ISort sort, IExpr expr) {
			this.symbol = sym;
			this.sort = sort;
			this.expression = expr;
		}
	}

}