/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib;
// FIXME- NEEDS REVIEW; use an interface?

import java.math.BigInteger;
import java.util.*;

import org.smtlib.IExpr.*;
import org.smtlib.ISort.*;
import org.smtlib.SMT.Configuration.SMTLIB;
import org.smtlib.impl.SMTExpr;
import org.smtlib.sexpr.ISexpr.ISeq;

/** This class is a visitor that type-checks a formula */
public class TypeChecker implements IVisitor</*@Nullable*/ ISort> {

    // TypeChecker used to extend the now-deleted IVisitor.NullVisitor to get these 25
    // node-type overrides for free, each silently returning null; NullVisitor was removed
    // since TypeChecker was its only real user (see git history). Deliberately made
    // fail-fast here instead of reproducing that silent no-op: verified empirically that
    // none of these 25 node types are ever actually visited anywhere in the full
    // ~11,000-test corpus across the full solver matrix, so throwing costs nothing today
    // -- but TypeChecker is only exercised via the mock "test" solver in the first place,
    // so a future test, theory addition, or new caller could still reach one of these for
    // real. A silent `return null` would let that pass through as an unchecked-but-wrong
    // sort with no signal at all; this throws loudly instead, so the first thing that
    // actually reaches one of these node types fails immediately and points straight back
    // here, rather than surfacing later as a confusing downstream symptom.
    @Override public ISort visit(IAttribute<?> e) throws VisitorException { throw new RuntimeException("TypeChecker.visit(IAttribute) reached: " + e); }
    @Override public ISort visit(IBinding e) throws VisitorException { throw new RuntimeException("TypeChecker.visit(IBinding) reached: " + e); }
    @Override public ISort visit(ISort.IDatatype e) throws VisitorException { throw new RuntimeException("TypeChecker.visit(ISort.IDatatype) reached: " + e); }
    @Override public ISort visit(IExpr.ISortDeclaration e) throws VisitorException { throw new RuntimeException("TypeChecker.visit(IExpr.ISortDeclaration) reached: " + e); }
    @Override public ISort visit(ISelector e) throws VisitorException { throw new RuntimeException("TypeChecker.visit(ISelector) reached: " + e); }
    @Override public ISort visit(IConstructor e) throws VisitorException { throw new RuntimeException("TypeChecker.visit(IConstructor) reached: " + e); }
    @Override public ISort visit(IDeclaration e) throws VisitorException { throw new RuntimeException("TypeChecker.visit(IDeclaration) reached: " + e); }
    @Override public ISort visit(IFunctionDeclaration e) throws VisitorException { throw new RuntimeException("TypeChecker.visit(IFunctionDeclaration) reached: " + e); }
    @Override public ISort visit(ICommand.IScript e) throws VisitorException { throw new RuntimeException("TypeChecker.visit(ICommand.IScript) reached: " + e); }
    @Override public ISort visit(ICommand e) throws VisitorException { throw new RuntimeException("TypeChecker.visit(ICommand) reached: " + e); }
    @Override public ISort visit(IExpr.IMatchCase e) throws VisitorException { throw new RuntimeException("TypeChecker.visit(IExpr.IMatchCase) reached: " + e); }
    @Override public ISort visit(IExpr.IPattern e) throws VisitorException { throw new RuntimeException("TypeChecker.visit(IExpr.IPattern) reached: " + e); }
    @Override public ISort visit(ILogic s) throws VisitorException { throw new RuntimeException("TypeChecker.visit(ILogic) reached: " + s); }
    @Override public ISort visit(ITheory s) throws VisitorException { throw new RuntimeException("TypeChecker.visit(ITheory) reached: " + s); }
    @Override public ISort visit(IResponse e) throws VisitorException { throw new RuntimeException("TypeChecker.visit(IResponse) reached: " + e); }
    @Override public ISort visit(IResponse.IError e) throws VisitorException { throw new RuntimeException("TypeChecker.visit(IResponse.IError) reached: " + e); }
    @Override public ISort visit(IResponse.IAssertionsResponse e) throws VisitorException { throw new RuntimeException("TypeChecker.visit(IResponse.IAssertionsResponse) reached: " + e); }
    @Override public ISort visit(IResponse.IAssignmentResponse e) throws VisitorException { throw new RuntimeException("TypeChecker.visit(IResponse.IAssignmentResponse) reached: " + e); }
    @Override public ISort visit(IResponse.IProofResponse e) throws VisitorException { throw new RuntimeException("TypeChecker.visit(IResponse.IProofResponse) reached: " + e); }
    @Override public ISort visit(IResponse.IValueResponse e) throws VisitorException { throw new RuntimeException("TypeChecker.visit(IResponse.IValueResponse) reached: " + e); }
    @Override public ISort visit(IResponse.IUnsatCoreResponse e) throws VisitorException { throw new RuntimeException("TypeChecker.visit(IResponse.IUnsatCoreResponse) reached: " + e); }
    @Override public ISort visit(IResponse.IUnsatAssumptionsResponse e) throws VisitorException { throw new RuntimeException("TypeChecker.visit(IResponse.IUnsatAssumptionsResponse) reached: " + e); }
    @Override public ISort visit(IResponse.IAttributeList e) throws VisitorException { throw new RuntimeException("TypeChecker.visit(IResponse.IAttributeList) reached: " + e); }
    @Override public ISort visit(org.smtlib.sexpr.ISexpr.ISeq e) throws VisitorException { throw new RuntimeException("TypeChecker.visit(ISexpr.ISeq) reached: " + e); }
    @Override public ISort visit(org.smtlib.sexpr.ISexpr.IToken<?> e) throws VisitorException { throw new RuntimeException("TypeChecker.visit(ISexpr.IToken) reached: " + e); }

    /** Compilation of errors */
    public List<IResponse> result = new LinkedList<IResponse>();

    /** A reference to the current symbol table */
    private SymbolTable symTable;

    /** A reference to the current configuration */
    private SMT.Configuration smtConfig;

    private ISymbol isClosed = null;

    /** The names under which a theory declares the sort of numeral, decimal and string literals
     *  (e.g. Ints' (NUMERAL Int)); each literal is sorted by looking its class's name up. */
    private static final ISymbol NUMERAL_SYM = new SMTExpr.Symbol("NUMERAL".intern());
    private static final ISymbol DECIMAL_SYM = new SMTExpr.Symbol("DECIMAL".intern());
    private static final ISymbol STRING_SYM = new SMTExpr.Symbol("STRING".intern());

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

    /** Reports a symbol that is not legal (see SMT.Configuration.isOKSymbol), which only the API (or
     *  declare-fun's name) can produce; returns true if it is not legal */
    protected boolean badSymbol(ISymbol s) {
        String msg = symbolError(smtConfig, s);
        if (msg == null) return false;
        error(msg, s.pos());
        return true;
    }

    /** The error message for a symbol that is not legal, or null if it is legal */
    static /*@Nullable*/ String symbolError(SMT.Configuration smtConfig, ISymbol s) {
        if (smtConfig.isOKSymbol(s.value())) return null;
        if (smtConfig.isReservedWord(s.value()))
            return "A reserved word may not be used as a symbol here: " + smtConfig.defaultPrinter.toString(s);
        return "Not a legal SMT-LIB symbol: " + smtConfig.utils.quote(s.value());
    }

    /** The error for a keyword that is not legal (see SMT.Configuration.isOKKeyword), which only
     *  the API can produce, or null if it is legal */
    static /*@Nullable*/ IResponse keywordError(SMT.Configuration smtConfig, IKeyword k) {
        if (smtConfig.isOKKeyword(k.value())) return null;
        return smtConfig.responseFactory.error("Not a legal SMT-LIB keyword: " + smtConfig.utils.quote(k.value()), k.pos());
    }

    /** Adds the error for a symbol that is not legal to errors; returns true if it is not legal */
    private static boolean badSymbol(SMT.Configuration smtConfig, ISymbol s, List<IResponse> errors) {
        String msg = symbolError(smtConfig, s);
        if (msg == null) return false;
        errors.add(smtConfig.responseFactory.error(msg, s.pos()));
        return true;
    }

    /** Reports a bound variable (sort parameter, if sort is true) with the name of a function (sort)
     *  symbol of the logic or its theories, which only --relax allows (SMT-LIB Remark 7); returns true
     *  if reported */
    protected boolean shadowsLogic(ISymbol s, boolean sort) {
        if (smtConfig.relax || !symTable.isLogicSymbol(s, sort)) return false;
        error((sort ? "A sort parameter may not have the name of a sort symbol of the logic: "
                    : "A bound variable may not have the name of a function symbol of the logic: ") + pr(s), s.pos());
        return true;
    }

    /** Reports a binder with no variables; returns true if the list is empty */
    protected boolean noVariables(List<?> list, String binder, IPos pos) {
        if (!list.isEmpty()) return false;
        error("At least one variable must be bound by " + binder, pos);
        return true;
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
            if (params != null) for (ISort.IParameter p : params) {
                if (f.shadowsLogic(p.symbol(), true)) errors = true;
                boolean b = symTable.addSortParameter(p.symbol(), false);
                if (!b) {
                    f.error("Duplicate sort parameters: " + p.symbol(),p.pos());
                    errors = true;
                }
            }
            if (!errors && expr != null) expr.accept(f);
            // A sort definition may contain only its own sort parameters, no global one (SMT-LIB 2.7, 4.2.3)
            if (!errors && expr != null && f.result.isEmpty()) {
                List<ISort.IParameter> own = new LinkedList<>();
                if (params != null) for (ISort.IParameter p : params) {
                    own.add(p);
                    own.add((ISort.IParameter) symTable.lookupSort(p.symbol()));
                }
                for (ISort.IParameter p : SymbolTable.parametersIn(expr, new LinkedList<ISort.IParameter>())) {
                    if (!own.contains(p)) {
                        f.error("A sort definition may not contain the global sort parameter "
                                + symTable.smtConfig.defaultPrinter.toString(p.symbol()), expr.pos());
                        break;
                    }
                }
            }
            // After the type check, which links the abbreviations in expr to their definitions
            if (f.result.isEmpty()) symTable.logicInUse.checkSortDeclaration(id,params,expr);
        } catch (IVisitor.VisitorException e) {
            f.error("Error while checking sort abbreviation: " + e.getMessage(),id.pos());
        } catch (Exception e) {
            f.error("INTERNAL ERROR: Exception while checking a sort abbreviation: " + e,id.pos());
        } finally {
            symTable.pop();
        }
        return f.result;
    }

    public static List<IResponse> checkFcn(SymbolTable symTable, IIdentifier id, List<ISort> sorts, ISort result, IPos pos) {
        List<IResponse> errors = new LinkedList<IResponse>();
        resolveFcnSort(symTable, id, sorts, result, pos, errors);
        return errors;
    }

    /** Checks a function signature as checkFcn does, adding any errors to errors; returns the
     *  signature with its sorts resolved in the current scope (so a sort parameter in scope
     *  becomes its IParameter), or null if there were errors. */
    public static /*@Nullable*/ IFcnSort resolveFcnSort(SymbolTable symTable, IIdentifier id, List<ISort> sorts, ISort result, IPos pos, List<IResponse> errors) {
        TypeChecker f = new TypeChecker(symTable);
        ISort[] newsorts = new ISort[sorts.size()];
        ISort newresult = null;
        try {
            for (int i = 0; i < newsorts.length; i++) {
                newsorts[i] = sorts.get(i).accept(f);
            }
            newresult = result.accept(f);
            try {
                symTable.logicInUse.checkFcnDeclaration(id,sorts,newresult,null);
            } catch (IVisitor.VisitorException e) {
                f.error(e.getMessage(), e.pos());
            }
        } catch (IVisitor.VisitorException e) {
            f.error("INTERNAL ERROR: Exception while checking a function declaration: " + e.getMessage(), pos);
        } catch (Exception e) {
            f.error("INTERNAL ERROR: Exception while checking a function declaration: " + e, null);
        }
        errors.addAll(f.result);
        if (!f.result.isEmpty()) return null;
        return symTable.smtConfig.sortFactory.createFcnSort(newsorts, newresult);
    }

    public static List<IResponse> checkFcn(SymbolTable symTable, IIdentifier id, List<IDeclaration> params, ISort result, IExpr expr) {
        TypeChecker f = new TypeChecker(symTable);
        symTable.push();
        try {
            for (IDeclaration p : params) {
                f.shadowsLogic(p.parameter(), false);
                if (p.sort().accept(f) != null) {
                    ISort.IFcnSort fs = symTable.smtConfig.sortFactory.createFcnSort(new ISort[0],p.sort());
                    // a parameter of a definition is a variable, of a sort that may be a sort parameter, not
                    // a polymorphic constant: an empty parameter list says so (#178)
                    SymbolTable.Entry entry = new SymbolTable.Entry(p.parameter(),fs,null,java.util.List.of());
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
            f.error("INTERNAL ERROR: Exception while checking a function definition: " + e.getMessage(),expr.pos());
        } catch (Exception e) {
            f.error("INTERNAL ERROR: Exception while checking a function definition: " + e,expr.pos());
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
        return check(symTable, expr, true);
    }

    /** Type-checks a term of any sort (e.g. a get-value term) and checks it against the logic in use, if any. */
    public static List<IResponse> checkTerm(SymbolTable symTable, IExpr expr) {
        return check(symTable, expr, false);
    }

    private static List<IResponse> check(SymbolTable symTable, IExpr expr, boolean requireBool) {
        TypeChecker f = new TypeChecker(symTable);
        try {
            ISort topsort = expr.accept(f);
            if (requireBool && topsort != null && !topsort.isBool()) {
                f.error("Expected an expression with Bool sort, not " + topsort, expr.pos());
            }
            try {
                if (symTable.logicInUse != null) symTable.logicInUse.validExpression(expr);
            } catch (IVisitor.VisitorException e) {
                f.error(e.getMessage(), e.pos());
            }
        } catch (IVisitor.VisitorException e) {
            f.error("Visitor Exception: " + e.getMessage(), e.pos());
        } catch (Exception e) {
            f.error("INTERNAL ERROR: Exception while checking an expression: " + e,expr.pos());
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
            f.error("INTERNAL ERROR: Exception while checking an assertion: " + e,expr.pos());
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
            @Override public Void visit(ILambda e) throws IVisitor.VisitorException { e.setSort(null); return super.visit(e); }
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
        if (e.value().signum() < 0) error("A numeral may not be negative: " + e.value(), e.pos());
        IFcnSort sort = symTable.lookup(0,NUMERAL_SYM);
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
            resultSort = ((IAsIdentifier)qhead).qualifier().accept(this);
            if (resultSort == null) return null;
            head = ((IAsIdentifier)qhead).head();
        } else {
            head = (IIdentifier)qhead;
        }
        String name = head.toString();
        // =, distinct, ite, store, select, and @ are all declared as par_fun_symbol_decl
        // entries (Core.smt2, ArraysEx.smt2, HO-Core.smt2) and used to be hardcoded here
        // because Utils.loadFuns() used to skip "par" declarations entirely -- now that it
        // doesn't, and SymbolTable.lookup() can unify against them (including the
        // :chainable/:pairwise/:left-assoc n-ary sugar =, distinct, and @ each need), they
        // fall through to the general lookup below like any other declared function, with
        // SymbolTable.lookup()'s `reason` output giving as specific a message as these
        // hardcoded branches used to (see its doc comment).
        List<TheorySignatures.Sig> sigs = TheorySignatures.lookup(head, false, symTable);
        if (sigs != null) return checkTheoryApplication(e, head, name, sigs, argSorts, resultSort);

        // (m t ...) for a map m abbreviates (@ m t ...) (SMT-LIB 2.7 Sec. 3.9)
        ISort mapSort = mapSort(head);
        if (mapSort != null) {
            save((ISymbol)head, mapSort);
            List<ISort> atArgs = new LinkedList<ISort>(argSorts);
            atArgs.add(0, mapSort);
            argSorts = atArgs;
            head = Utils.AT;
        }
        StringBuilder reason = new StringBuilder();
        ISort matchedResultSort = symTable.lookup(head,argSorts,resultSort,reason);
        if (matchedResultSort == null && symTable.realsIntsTheorySet) {
            matchedResultSort = lookupReadingIntAsReal(head, argSorts, resultSort);
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
            if (mapSort != null) msg = "(" + name + " ...) is read as (@ " + name + " ...): " + msg;
            error(msg,e.pos());
            return null;
        } else if (e.args().isEmpty()) {
            // (c) for a constant c: an application must have at least one argument
            error("The function symbol " + name + " takes no arguments, so it is written without parentheses", e.pos());
            return null;
        } else {
            return save(e,matchedResultSort);
        }
    }

    /** The number of selectors of constructor c of the datatype sort delta, or -1 if c is not one */
    private int constructorArity(ISymbol c, ISort delta) {
        List<SymbolTable.Entry> entries = symTable.lookup(c);
        if (entries != null) {
            for (SymbolTable.Entry en : entries) {
                int k = en.sort.argSorts().length;
                if (symTable.lookupInstance(k, c, delta) != null) return k;
            }
        }
        return -1;
    }

    /** The sort of head if it is a variable or constant of a -> sort, else null */
    private /*@Nullable*/ ISort mapSort(IIdentifier head) {
        if (!(head instanceof ISymbol)) return null;
        ISort s;
        Variable v = currentScope.get((ISymbol)head);
        if (v != null) {
            s = v.sort;
        } else {
            IFcnSort fs = symTable.lookup(0, head);
            s = fs == null ? null : fs.resultSort();
        }
        if (s == null) return null;
        ISort x = s.expand();
        return (x instanceof ISort.IApplication && Utils.ARROW.equals(((ISort.IApplication)x).family().headSymbol())) ? s : null;
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
        return Utils.BITVEC_SYM.equals(pid.head());
    }

    /** With Ints and Reals (Reals_Ints), an application that matches no signature as written is
     *  retried with Int arguments read as Real (to_real). AUFLIRA's and AUFNIRA's :extensions state
     *  this for (op Real Real s) with one Int and one Real argument, and for (/ Int Int); jSMTLIB
     *  applies it to every arity, to polymorphic =, distinct and ite, and to every logic with
     *  Reals_Ints (#211). The first retry reads every Int as Real; the second, for a function with
     *  both Int and Real parameters, only the Ints whose parameter is Real. Returns the result
     *  sort, or null if neither retry matches; the caller's reason then explains the failure
     *  against the sorts as written. */
    private /*@Nullable*/ ISort lookupReadingIntAsReal(IIdentifier head, List<ISort> argSorts, /*@Nullable*/ ISort resultSort) throws IVisitor.VisitorException {
        boolean hasInt = false;
        for (ISort sort: argSorts) if (isIntSort(sort)) hasInt = true;
        if (!hasInt) return null;
        ISort realSort = makeReal();
        List<ISort> allReal = new LinkedList<ISort>();
        for (ISort sort: argSorts) allReal.add(isIntSort(sort) ? realSort : sort);
        ISort result = symTable.lookup(head,allReal,resultSort,new StringBuilder());
        if (result != null) return result;
        List<SymbolTable.Entry> entries = symTable.lookup(head);
        if (entries == null) return null;
        for (SymbolTable.Entry entry: entries) {
            ISort[] declared = entry.sort.argSorts();
            if (entry.parameters != null || declared.length != argSorts.size()) continue;
            List<ISort> args = new LinkedList<ISort>();
            for (int k = 0; k < declared.length; k++) {
                ISort sort = argSorts.get(k);
                args.add(isIntSort(sort) && isRealSort(declared[k]) ? realSort : sort);
            }
            result = symTable.lookup(head,args,resultSort,new StringBuilder());
            if (result != null) return result;
        }
        return null;
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

    /** makeBitVec(length), or an error at pos (and null) if length is too large for an int */
    private /*@Nullable*/ ISort makeBitVec(long length, IPos pos) throws IVisitor.VisitorException {
        if (length > Integer.MAX_VALUE) {
            error("The bit-vector width " + length + " is too large (at most " + Integer.MAX_VALUE + ")", pos);
            return null;
        }
        return makeBitVec((int)length);
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
        return Utils.FLOATINGPOINT_SYM.equals(pid.head());
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
        IFcnSort sort = symTable.lookup(0,NUMERAL_SYM);
        return sort == null ? null : sort.resultSort();
    }

    @Override
    /*@checkers.igj.quals.ReadOnly*/
    public /*@Nullable*/ ISort visit(ISymbol e) {
        IFcnSort sort = null;
        String ambiguous;
        String value = e.value();
        if (Utils.WILDCARD.equals(value)) {
            error("The _ wildcard may only appear in match patterns", e.pos());
            return null;
        }
        if (badSymbol(e)) return null;
        if (Utils.TRUE.equals(e) || Utils.FALSE.equals(e)) {
            return save(e,symTable.smtConfig.sortFactory.Bool());
        } else {
            Variable v = currentScope.get(e);
            if (v != null) {
                if (isClosed == null && !v.closed) isClosed = e;
                return save(e,v.sort);
            }
            if ((sort=symTable.lookup(0,e))==null) {
                // A declared function is not a term (SMT-LIB 2.7 Remark 10); lookup's reason says so
                StringBuilder reason = new StringBuilder();
                symTable.lookup(e, new LinkedList<ISort>(), null, reason);
                List<SymbolTable.Entry> entries = symTable.lookup(e);
                if (reason.length() > 0 && entries != null && entries.size() == 1
                        && entries.get(0).sort.argSorts().length > 0) {
                    reason.append(" and cannot be used as a term without arguments").append(functionAsTermHint(e, entries.get(0).sort));
                }
                error(reason.length() > 0 ? reason.toString() : "Unknown constant symbol " + value, e.pos());
                return null;
            } else if (symTable.undeterminedConstant(e)) {
                error("The sort of " + value + " is not determined; qualify it with as", e.pos());
                return null;
            } else if ((ambiguous = symTable.ambiguousConstant(e)) != null) {
                error(ambiguous, e.pos());
                return null;
            } else {
                return save(e,sort.resultSort());
            }
        }
    }


    @Override
    public /*@Nullable*/ISort visit(IDecimal e) {
        if (e.value().signum() < 0) error("A decimal may not be negative: " + e.value().toPlainString(), e.pos());
        IFcnSort sort = symTable.lookup(0,DECIMAL_SYM);
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
        if (!smtConfig.isOKString(e.value())) {
            int c = e.value().chars().filter(ch -> !smtConfig.isOKString(String.valueOf((char)ch))).findFirst().getAsInt();
            error("A string literal may not contain the character with code " + c, e.pos());
        }
        IFcnSort sort = symTable.lookup(0,STRING_SYM);
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
        // parsed text never gets here (a parse error stops the command); an API-built term can (#146)
        error("The expression contains an error node: " + e.value(), e.pos());
        return null;
    }

    /** For a declared function f used as a term (#191): with HO-Core, how to write a function-valued term
     *  instead (a constant of the map sort, or a lambda); without it, that such terms need HO-Core */
    private String functionAsTermHint(ISymbol f, IFcnSort sig) {
        if (symTable.lookupSort(Utils.ARROW) == null) return " (function-valued terms need a logic with HO-Core)";
        ISort[] args = sig.argSorts();
        StringBuilder sort = new StringBuilder("(->");
        StringBuilder vars = new StringBuilder();
        StringBuilder app = new StringBuilder("(").append(pr(f));
        for (int i = 0; i < args.length; i++) {
            String x = args.length == 1 ? "x" : "x" + (i + 1);
            sort.append(' ').append(pr(args[i]));
            vars.append(i == 0 ? "" : " ").append('(').append(x).append(' ').append(pr(args[i])).append(')');
            app.append(' ').append(x);
        }
        sort.append(' ').append(pr(sig.resultSort())).append(')');
        return "; for a function-valued term, declare " + pr(f) + " as a constant of sort " + sort
                + ", or use (lambda (" + vars + ") " + app + "))";
    }

    /** Checks an application of a bit-vector or floating-point function against its signatures
     *  (TheorySignatures), in this order: version, argument count, the sort of each argument,
     *  matching sorts, indices, the `as` qualifier's sort (asSort, if not null); returns the result
     *  sort, or null after reporting an error */
    private /*@Nullable*/ ISort checkTheoryApplication(IFcnExpr e, IIdentifier head, String name,
            List<TheorySignatures.Sig> sigs, List<ISort> argSorts, /*@Nullable*/ ISort asSort)
            throws IVisitor.VisitorException {
        if (!theoryVersion(sigs.get(0), name, head)) return null;
        TheorySignatures.Sig sig = null;
        for (TheorySignatures.Sig s : sigs) if (s.fits(argSorts.size())) sig = s;
        if (sig == null) {
            error("The " + name + " function should have " + TheorySignatures.arities(sigs), head.pos());
            return null;
        }
        for (int i = 0; i < argSorts.size(); i++) {
            if (!hasKind(argSorts.get(i), sig.kind(i))) {
                kindError(name, e, i, sig.kind(i).description, argSorts.get(i));
                return null;
            }
        }
        // The sort shared by the same-sort arguments, and the result of a SAME signature
        ISort first = null;
        for (int i = 0; i < argSorts.size(); i++) {
            TheorySignatures.Kind k = sig.kind(i);
            if (k != TheorySignatures.Kind.BV && k != TheorySignatures.Kind.FP) continue;
            if (first == null) {
                first = argSorts.get(i);
            } else if (sig.same() && !first.equals(argSorts.get(i))) {
                sortMismatch(first, argSorts.get(i), e);
                return null;
            }
        }
        int[] widths = new int[argSorts.size()];
        for (int i = 0; i < widths.length; i++) widths[i] = bitvecSize(argSorts.get(i));
        int[] indices = theoryIndices(sig, head, name, e, argSorts, widths);
        if (indices == null) return null;
        ISort result = theoryResult(sig, first, widths, indices, e.pos());
        if (result == null) return null;
        if (asSort != null && !asSort.equals(result)) {
            error(name + " has result sort " + pr(result) + ", expected " + pr(asSort) + " (from the `as` qualifier)", e.pos());
            return null;
        }
        return save(e, result);
    }

    /** Checks an indexed bit-vector or floating-point constant against its signature */
    private /*@Nullable*/ ISort checkTheoryConstant(IParameterizedIdentifier e, TheorySignatures.Sig sig)
            throws IVisitor.VisitorException {
        if (!theoryVersion(sig, e.toString(), e)) return null;
        int[] indices = theoryIndices(sig, e, e.toString(), null, List.of(), new int[0]);
        if (indices == null) return null;
        ISort result = theoryResult(sig, null, new int[0], indices, e.pos());
        return result == null ? null : save(e, result);
    }

    /** Whether the configured SMT-LIB version has sig, reporting an error if not */
    private boolean theoryVersion(TheorySignatures.Sig sig, String name, IIdentifier head) {
        if (smtConfig.atLeastVersion(sig.since())) return true;
        error("The " + name + " function requires SMT-LIB " + sig.since() + " or later", head.pos());
        return false;
    }

    private boolean hasKind(ISort s, TheorySignatures.Kind k) {
        return switch (k) {
            case BV -> isBitVec(s);
            case BV1 -> isBitVec(s) && bitvecSize(s) == 1;
            case FP -> isFloatingPoint(s);
            case RM -> isRoundingMode(s);
            case INT -> isIntSort(s);
            case FP_REAL_BV -> isFloatingPoint(s) || isRealSort(s) || isBitVec(s);
        };
    }

    /** The indices of head, checked against sig; null after reporting an error. e is the
     *  application, or null for a constant. */
    private /*@Nullable*/ int[] theoryIndices(TheorySignatures.Sig sig, IIdentifier head, String name,
            /*@Nullable*/ IFcnExpr e, List<ISort> argSorts, int[] widths) {
        if (sig.indices() == 0) return new int[0];
        IParameterizedIdentifier pid = (IParameterizedIdentifier)head;
        if (!checkIndices(pid, sig.indices())) return null;
        int[] indices = new int[sig.indices()];
        for (int i = 0; i < indices.length; i++) indices[i] = ((INumeral) pid.indices().get(i)).intValue();
        if (sig.check() == null) return indices;
        TheorySignatures.Problem p = sig.check().check(pid.head().value(), indices, widths);
        if (p == null) return indices;
        if (p.index() >= 0) error(p.message(), pid.indices().get(p.index()).pos());
        else if (p.arg() >= 0 && e != null) kindError(name, e, p.arg(), p.message(), argSorts.get(p.arg()));
        else error(p.message(), pid.pos());
        return null;
    }

    /** The result sort of sig; null after reporting an error */
    private /*@Nullable*/ ISort theoryResult(TheorySignatures.Sig sig, /*@Nullable*/ ISort first, int[] widths,
            int[] indices, IPos pos) throws IVisitor.VisitorException {
        return switch (sig.result()) {
            case SAME -> first;
            case BOOL -> {
                ISort b = smtConfig.sortFactory.Bool();
                b.accept(this);
                yield b;
            }
            case INT -> makeInt();
            case REAL -> makeReal();
            case BITVEC -> makeBitVec(sig.widths().of(widths, indices)[0], pos);
            case FLOATINGPOINT -> {
                long[] ebsb = sig.widths().of(widths, indices);
                yield makeFloatingPoint((int)ebsb[0], (int)ebsb[1]); // also checks eb > 1, sb > 1
            }
        };
    }

    /** Reports that argument i of e, an application of name, does not have the sort described by kind */
    private void kindError(String name, IFcnExpr e, int i, String kind, ISort s) {
        String which = e.args().size() == 1 ? "The argument" : "The " + ordinal(i + 1) + " argument";
        error(which + " of " + name + " must have " + kind + ", not " + pr(s), e.args().get(i).pos());
    }

    /** Reports that an argument's sort t differs from the sort s of an earlier argument it must match */
    private void sortMismatch(ISort s, ISort t, IFcnExpr e) {
        error("The sorts must match: " + pr(s) + " vs. " + pr(t), e.pos());
    }

    private static String ordinal(int k) {
        String[] words = {"first", "second", "third", "fourth", "fifth", "sixth", "seventh", "eighth", "ninth", "tenth"};
        if (k <= words.length) return words[k - 1];
        int t = k % 100;
        return k + (t >= 11 && t <= 13 ? "th" : k % 10 == 1 ? "st" : k % 10 == 2 ? "nd" : k % 10 == 3 ? "rd" : "th");
    }

    /** checkNumeralIndices, with the message for an indexed theory function or constant */
    private boolean checkIndices(IExpr.IParameterizedIdentifier pid, int count) {
        return checkNumeralIndices(pid, count, "The " + pid.head() + " identifier should have "
                + (count == 1 ? "one numeral index" : "two numeral indices"));
    }

    /** Checks that pid has exactly {@code count} indices and all are INumeral.
     *  Records {@code errorMsg} at pid.pos() and returns false if not. */
    private boolean checkNumeralIndices(IExpr.IParameterizedIdentifier pid, int count, String errorMsg) {
        if (pid.indices().size() != count) { error(errorMsg, pid.pos()); return false; }
        for (IIndex idx : pid.indices()) {
            if (!(idx instanceof INumeral)) { error(errorMsg, pid.pos()); return false; }
        }
        for (IIndex idx : pid.indices()) {
            String tooLarge = Utils.indexTooLarge((INumeral)idx);
            if (tooLarge != null) { error(tooLarge, idx.pos()); return false; }
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

    /** Checks a Strings-theory constant (_ char H): H is a hexadecimal of 1-5 digits, at most #x2FFFF. */
    private /*@Nullable*/ ISort checkChar(IParameterizedIdentifier e, ISort stringSort) {
        if (e.indices().size() != 1 || !(e.indices().get(0) instanceof IHexLiteral)) {
            error("Expected exactly one hexadecimal index in a char identifier", e.pos());
            return null;
        }
        IHexLiteral h = (IHexLiteral) e.indices().get(0);
        if (h.length() > 5) {
            error("The index of a char identifier has at most 5 hex digits", h.pos());
            return null;
        }
        if (h.intValue().compareTo(BigInteger.valueOf(0x2FFFF)) > 0) {
            error("The code point of a char identifier must be at most #x2FFFF", h.pos());
            return null;
        }
        return save(e, stringSort);
    }

    @Override
    public /*@Nullable*/ ISort visit(IParameterizedIdentifier e) throws IVisitor.VisitorException {
        requireVersionForSymbolIndex(e);
        IFcnSort sort = null;
        List<TheorySignatures.Sig> sigs = TheorySignatures.lookup(e, true, symTable);
        if (sigs != null) return checkTheoryConstant(e, sigs.get(0));

        if (Utils.CHAR.equals(e.head())) {
                IFcnSort ssort = symTable.lookup(0,STRING_SYM);
            if (ssort != null) return checkChar(e, ssort.resultSort());
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
        // (as c S) as a term; in a function application visit(IFcnExpr) checks the qualifier
        ISort s = e.qualifier().accept(this);
        if (s == null) return null;
        IIdentifier head = e.head();
        boolean isVariable = head instanceof ISymbol && currentScope.get(head) != null;
        if (!isVariable && symTable.lookup(head) != null) {
            // A declared constant, possibly overloaded or par-polymorphic: S selects the declaration
            StringBuilder reason = new StringBuilder();
            ISort r = symTable.lookup(head, Collections.<ISort>emptyList(), s, reason);
            if (r == null) {
                error(reason.length() > 0 ? reason.toString() : "Unknown constant symbol " + pr(head), e.pos());
                return null;
            }
            return save(e,r);
        }
        ISort hs = head.accept(this);
        if (hs == null) return null;
        if (!hs.equals(s)) {
            error(pr(head) + " has sort " + pr(hs) + ", expected " + pr(s) + " (from the `as` qualifier)", e.pos());
            return null;
        }
        return save(e,s);
    }

    /** The body of the innermost quantifier being checked (the only place a :pattern may appear), or null. */
    protected /*@Nullable*/ IExpr quantifierBody = null;

    /** Checks that a pattern term is binder-free and has no annotations (SMT-LIB 2.7, Section 3.6.5);
     *  returns false, recording an error, if it is not. */
    protected boolean checkPatternTerm(IExpr t) {
        if (t instanceof IForall || t instanceof IExists || t instanceof ILet || t instanceof IExpr.IMatch || t instanceof IExpr.ILambda) {
            result.add(smtConfig.responseFactory.error("A pattern term may not contain a binder",t.pos()));
            return false;
        }
        if (t instanceof IAttributedExpr) {
            result.add(smtConfig.responseFactory.error("A pattern term may not contain an annotation",t.pos()));
            return false;
        }
        if (t instanceof IFcnExpr) {
            for (IExpr a: ((IFcnExpr)t).args()) if (!checkPatternTerm(a)) return false;
        }
        return true;
    }

    @Override
    public /*@Nullable*/ ISort visit(IAttributedExpr e) throws IVisitor.VisitorException {
        boolean isQuantifierBody = e == quantifierBody;
        ISymbol savedIsClosed = isClosed;
        isClosed = null;
        boolean errors = false;
        ISort resultSort = null;
        try {
            resultSort = save(e,e.expr().accept(this));
            if (e.attributes().isEmpty()) {
                error("An annotated term must have at least one attribute", e.pos());
                errors = true;
            }
            for (IAttribute<?> a: e.attributes()) {
                String name = a.keyword().value();
                IResponse keyErr = keywordError(smtConfig, a.keyword());
                if (keyErr != null) {
                    result.add(keyErr);
                    errors = true;
                } else if (a.attrValue() instanceof ISymbol && badSymbol((ISymbol)a.attrValue())) {
                    errors = true;
                } else if (name.equals(":named")) { // FIXME - use a canonical representation
                    IAttributeValue v = a.attrValue();
                    if (!(v instanceof ISymbol)) {
                        result.add(smtConfig.responseFactory.error("Expected a symbol after :named",v==null?a.keyword().pos():v.pos()));
                        errors = true;
                        continue;
                    }
                    ISort.IFcnSort fcnSort = smtConfig.sortFactory.createFcnSort(new ISort[0],resultSort);
                    SymbolTable.Entry entry = new SymbolTable.Entry((ISymbol)v,fcnSort,null,null);
                    if (!symTable.add(entry, false, false)) { 
                        result.add(smtConfig.responseFactory.error("Symbol " + v.toString() + " is already defined",v.pos()));
                        errors = true;
                    }
                    if (isClosed != null) {
                        result.add(smtConfig.responseFactory.error("The expression being named is not closed - this symbol is a variable: " + smtConfig.defaultPrinter.toString(isClosed),isClosed.pos()));
                        errors = true;
                    }
                } else if (name.equals(":pattern")) {
                    IAttributeValue v = a.attrValue();
                    if (!isQuantifierBody) {
                        result.add(smtConfig.responseFactory.error("A :pattern may only annotate the body of a forall or exists",a.keyword().pos()));
                        errors = true;
                    } else if (v instanceof IExpr.IPatternTerms) {
                        for (IExpr ex: ((IExpr.IPatternTerms)v).terms()) {
                            if (checkPatternTerm(ex)) ex.accept(this); else errors = true;
                        }
                    } else if (v instanceof ISeq) {
                        result.add(smtConfig.responseFactory.error("A :pattern value must be a list of terms (IExpr.IFactory.patternTerms), not an s-expression",v.pos()));
                        errors = true;
                    } else {
                        result.add(smtConfig.responseFactory.error("Expected a sequence after :pattern",v==null?a.keyword().pos():v.pos()));
                        errors = true;
                    }
                }
            }
        } finally {
            isClosed = isClosed == null ? savedIsClosed : isClosed;
        }
        if (errors) return null;
        return resultSort;
    }

    protected Map<ISymbol,Variable> currentScope = new HashMap<ISymbol,Variable>();
    protected List<Map<ISymbol,Variable>> parameters = new LinkedList<Map<ISymbol,Variable>>();

    @Override
    public /*@Nullable*/ ISort visit(IForall e) throws IVisitor.VisitorException {
        if (noVariables(e.parameters(), "forall", e.pos())) return null;
        Map<ISymbol,Variable> saved = new HashMap<ISymbol,Variable>();
        saved.putAll(currentScope);
        parameters.add(0,saved);
        boolean errors = false;
        Set<ISymbol> seen = new HashSet<>();
        for (IExpr.IDeclaration decl : e.parameters()) {
            if (badSymbol(decl.parameter()) || shadowsLogic(decl.parameter(), false)) errors = true;
            else if (!seen.add(decl.parameter())) {
                error("Parameter list has a duplicate name: " + pr(decl.parameter()), decl.parameter().pos());
                errors = true;
            }
            ISort res = decl.sort().accept(this);
            if (res == null) errors = true;
            else currentScope.put(decl.parameter(),new Variable(decl.parameter(),decl.sort(),null,false));
        }
        IExpr savedQuantifierBody = quantifierBody;
        try {
            if (errors) return null;
            quantifierBody = e.expr();
            ISort s = e.expr().accept(this);
            return save(e,s);
        } finally {
            quantifierBody = savedQuantifierBody;
            currentScope = parameters.remove(0);
        }
    }

    @Override
    public /*@Nullable*/ ISort visit(IExists e) throws IVisitor.VisitorException {
        if (noVariables(e.parameters(), "exists", e.pos())) return null;
        Map<ISymbol,Variable> saved = new HashMap<ISymbol,Variable>();
        saved.putAll(currentScope);
        parameters.add(0,saved);
        boolean errors = false;
        Set<ISymbol> seen = new HashSet<>();
        for (IExpr.IDeclaration decl : e.parameters()) {
            if (badSymbol(decl.parameter()) || shadowsLogic(decl.parameter(), false)) errors = true;
            else if (!seen.add(decl.parameter())) {
                error("Parameter list has a duplicate name: " + pr(decl.parameter()), decl.parameter().pos());
                errors = true;
            }
            ISort res = decl.sort().accept(this);
            if (res == null) errors = true;
            else currentScope.put(decl.parameter(),new Variable(decl.parameter(),decl.sort(),null,false));
        }
        IExpr savedQuantifierBody = quantifierBody;
        try {
            if (errors) return null;
            quantifierBody = e.expr();
            ISort s = e.expr().accept(this);
            return save(e,s);
        } finally {
            quantifierBody = savedQuantifierBody;
            currentScope = parameters.remove(0);
        }
    }

    /** Type-checks a lambda expression: {@code (lambda (sorted_var+) term)}, SMT-LIB 2.7ff
     *  (the optional HO-Core theory -- see {@code SMT/logics/HO-Core.smt2}).
     *  <P>
     *  Parameter/body scoping is identical to visit(IForall)/visit(IExists) above: push a
     *  new scope, type-check each parameter declaration into it (catching duplicate names),
     *  then type-check the body in that scope. Unlike a quantifier, though, a lambda's body
     *  is not required to be Bool -- it can be any sort -- and the lambda expression's own
     *  computed sort is not its body's sort but the <I>function</I> sort mapping its
     *  parameters' sorts to its body's sort.
     *  <P>
     *  Design decision (see jSMTLIB issue #125): SMT-LIB 2.7 also introduces a
     *  {@code (-> sort+ sort)} function-sort constructor for exactly this purpose, and that
     *  constructor already exists in this codebase -- not as new work for lambda, but as an
     *  ordinary theory-declared sort: HO-Core.smt2 declares {@code :sorts ( (-> 2
     *  :right-assoc) )}, so {@code ->} is a plain 2-ary sort family, resolved through the
     *  same generic path as any other declared sort (visit(ISort.IApplication) already has a
     *  special case unfolding {@code ->} via its :right-assoc attribute when given more than
     *  its declared arity of 2 arguments -- see the comment there). So rather than fabricating
     *  a placeholder sort (e.g. just the body's sort) or throwing a not-yet-supported error,
     *  this builds an (unchecked) {@code (-> paramSort1 ... paramSortN bodySort)}
     *  sort-application node and runs it through this same type checker, exactly the way
     *  makeBitVec()/makeFloatingPoint()/makeReal() above already construct-then-check a sort
     *  expression rather than hand-building one. Two honest, non-fabricated outcomes follow
     *  directly from reusing that existing machinery, with no new logic of its own:
     *  <UL>
     *  <LI>If the active logic/theory declares {@code ->} (i.e. HO-Core is loaded, as with
     *  {@code (set-logic ALL)}), the lambda's sort is the real, correctly-computed function
     *  sort -- e.g. {@code (-> Int Int)} for {@code (lambda ((x Int)) (+ x 1))}.</LI>
     *  <LI>If it does not, this reports the same "No such sort symbol declared: -&gt;" error
     *  that any other undeclared sort symbol would get -- exactly like using any other
     *  theory-specific symbol without its theory loaded, not a crash or a silently-wrong
     *  sort.</LI>
     *  </UL>
     */
    @Override
    public /*@Nullable*/ ISort visit(ILambda e) throws IVisitor.VisitorException {
        // lambda is new in SMT-LIB 2.7 (HO-Core) -- gate on the configured version the same
        // way visit(IExpr.IMatch) below already gates match and its wildcard pattern on
        // SMTLIB.V26/V27, rather than silently accepting it under an older configured version.
        if (!smtConfig.atLeastVersion(SMTLIB.V27)) {
            error("The lambda expression requires SMT-LIB " + SMTLIB.V27 + " or later", e.pos());
            return null;
        }
        if (noVariables(e.parameters(), "lambda", e.pos())) return null;
        Map<ISymbol,Variable> saved = new HashMap<ISymbol,Variable>();
        saved.putAll(currentScope);
        parameters.add(0,saved);
        boolean errors = false;
        Set<ISymbol> seen = new HashSet<>();
        List<ISort> paramSorts = new LinkedList<ISort>();
        for (IExpr.IDeclaration decl : e.parameters()) {
            if (badSymbol(decl.parameter()) || shadowsLogic(decl.parameter(), false)) errors = true;
            else if (!seen.add(decl.parameter())) {
                error("Parameter list has a duplicate name: " + pr(decl.parameter()), decl.parameter().pos());
                errors = true;
            }
            ISort res = decl.sort().accept(this);
            if (res == null) errors = true;
            else {
                currentScope.put(decl.parameter(),new Variable(decl.parameter(),decl.sort(),null,false));
                paramSorts.add(decl.sort());
            }
        }
        try {
            if (errors) return null;
            ISort bodySort = e.expr().accept(this);
            if (bodySort == null) return null;
            List<ISort> arrowArgs = new LinkedList<ISort>(paramSorts);
            arrowArgs.add(bodySort);
            IIdentifier arrowId = smtConfig.exprFactory.symbol("->");
            ISort arrowSort = smtConfig.sortFactory.createSortExpression(arrowId, arrowArgs);
            ISort checkedArrowSort = arrowSort.accept(this);
            return save(e, checkedArrowSort);
        } finally {
            currentScope = parameters.remove(0);
        }
    }

    @Override
    public /*@Nullable*/ ISort visit(ILet e) throws IVisitor.VisitorException {
        if (noVariables(e.bindings(), "let", e.pos())) return null;
        Map<ISymbol,Variable> newdecls = new HashMap<ISymbol,Variable>();
        Map<ISymbol,Variable> saved = new HashMap<ISymbol,Variable>();
        saved.putAll(currentScope);
        parameters.add(0,saved);
        try {
            boolean anyErrors = false;
            Set<ISymbol> seen = new HashSet<>();
            for (IExpr.IBinding decl : e.bindings()) {
                if (badSymbol(decl.parameter()) || shadowsLogic(decl.parameter(), false)) anyErrors = true;
                else if (!seen.add(decl.parameter())) {
                    error("Parameter list has a duplicate name: " + pr(decl.parameter()), decl.parameter().pos());
                    anyErrors = true;
                }
                IExpr expr = decl.expr();
                // Whether referencing this let-bound variable is itself closed depends on
                // whether ITS OWN defining expression is closed -- not just on the mere
                // existence of that expression (a stale check this used to make: a
                // non-null expression was treated as automatically closed regardless of
                // its content, missing e.g. (forall ((q Bool)) (let ((r q)) ...)), where
                // r's value q is itself an outer free variable). Save/restore isClosed
                // around checking expr the same way visit(IAttributedExpr) does, so this
                // nested check doesn't consume or duplicate an outer :named check's own
                // tracking.
                ISymbol savedIsClosed = isClosed;
                isClosed = null;
                ISort s = expr.accept(this);
                boolean exprIsClosed = isClosed == null;
                isClosed = isClosed == null ? savedIsClosed : isClosed;
                if (s == null) anyErrors = true;
                else {
                    newdecls.put(decl.parameter(),new Variable(decl.parameter(),s,expr,exprIsClosed));
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
        List<ISymbol> allCtors = (scrutineeSort instanceof ISort.IApplication)
                ? symTable.datatypeConstructors(((ISort.IApplication)scrutineeSort).family()) : null;
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

                if (!pat.parenthesized()) {
                    if (Utils.WILDCARD.equals(pat.constructor().value())) {
                        if (!smtConfig.atLeastVersion(SMTLIB.V27)) {
                            error("The _ wildcard in match patterns requires SMT-LIB V2.7 or later", pat.constructor().pos());
                            anyErrors = true;
                        }
                        hasVariableOrWildcard = true;
                    } else if (badSymbol(pat.constructor())) {
                        anyErrors = true;
                    } else {
                        IFcnSort ctorSort = symTable.lookupInstance(0, pat.constructor(), scrutineeSort);
                        if (ctorSort == null) {
                            // Not a nullary constructor of this sort — treat as variable binding
                            if (shadowsLogic(pat.constructor(), false)) anyErrors = true;
                            currentScope.put(pat.constructor(), new Variable(pat.constructor(), scrutineeSort, null, false));
                            hasVariableOrWildcard = true;
                        } else {
                            coveredCtors.add(pat.constructor().value());
                        }
                    }
                } else {
                    // (c x1 ... xk): c a constructor of the scrutinee's datatype with k > 0 selectors
                    int arity = pat.params().size();
                    IFcnSort ctorSort = symTable.lookup(arity, pat.constructor());
                    IFcnSort instance = ctorSort == null ? null : symTable.lookupInstance(arity, pat.constructor(), scrutineeSort);
                    int ctorArity = allCtors.contains(pat.constructor()) ? constructorArity(pat.constructor(), scrutineeSort) : -1;
                    if (ctorArity == 0 && smtConfig.relax) {
                        // --relax accepts (c) for a nullary constructor c, with the parser's warning
                        coveredCtors.add(pat.constructor().value());
                    } else if (ctorArity == 0) {
                        error("The constructor " + pat.constructor().value() + " takes no arguments, so its pattern is written without parentheses",
                                pat.pos());
                        anyErrors = true;
                    } else if (ctorArity > 0 && ctorArity != arity) {
                        error("The constructor " + pat.constructor().value() + " takes " + ctorArity
                                + " argument" + (ctorArity == 1 ? "" : "s") + ", not " + arity, pat.pos());
                        anyErrors = true;
                    } else if (ctorSort == null) {
                        error("Unknown constructor: " + pat.constructor().value(), pat.constructor().pos());
                        anyErrors = true;
                    } else if (instance == null) {
                        error("Constructor " + pat.constructor().value() + " has result sort "
                                + pr(ctorSort.resultSort()) + " but scrutinee has sort " + pr(scrutineeSort),
                                pat.constructor().pos());
                        anyErrors = true;
                    } else if (ctorArity < 0) {
                        error(pat.constructor().value() + " is not a constructor of the datatype " + pr(scrutineeSort),
                                pat.constructor().pos());
                        anyErrors = true;
                    } else {
                        coveredCtors.add(pat.constructor().value());
                        ISort[] argSorts = instance.argSorts();
                        List<IExpr.ISymbol> params = pat.params();
                        Set<String> patternVarsSeen = new HashSet<>();
                        for (int i = 0; i < params.size(); i++) {
                            if (Utils.WILDCARD.equals(params.get(i).value())) {
                                if (!smtConfig.atLeastVersion(SMTLIB.V27)) {
                                    error("The _ wildcard in match patterns requires SMT-LIB V2.7 or later", params.get(i).pos());
                                    anyErrors = true;
                                }
                            } else if (badSymbol(params.get(i)) || shadowsLogic(params.get(i), false)) {
                                anyErrors = true;
                            } else {
                                if (!patternVarsSeen.add(params.get(i).value())) {
                                    error("Duplicate variable in match pattern: " + params.get(i).value(), params.get(i).pos());
                                    anyErrors = true;
                                } else {
                                    currentScope.put(params.get(i), new Variable(params.get(i), argSorts[i], null, false));
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
                    + (def.intArity() == 1 ? " argument" : " arguments") + ", not " + args.size(), s.pos());
            return null;
        }
        if (errors) return null;
        if (s.parenthesized() && args.isEmpty()) {
            error("The sort symbol " + pr(f) + " takes no parameters, so it is written without parentheses", s.pos());
            return null;
        }
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
        // a symbol-table signature, never parsed as a sort; an API-built declaration can use one (#146)
        error("A function signature is not a sort: " + s, s.pos());
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
        } else if (cmd instanceof ICommand.Idefine_fun_rec) {
            // Checked before Idefine_fun below: C_define_fun_rec extends C_define_fun (see
            // issue #43), so its instances are also instanceof Idefine_fun -- the more specific
            // interface must be checked first, mirroring Ideclare_const vs. Ideclare_fun above.
            requireVersion(smtConfig, SMT.Configuration.SMTLIB.V25, "define-fun-rec", errors);
            ICommand.Idefine_fun_rec c = (ICommand.Idefine_fun_rec)cmd;
            validateUserId(smtConfig, c.symbol(), errors);
            if (errors.isEmpty()) validateUniqueDeclarations(smtConfig, c.parameters(), errors);
        } else if (cmd instanceof ICommand.Idefine_fun) {
            ICommand.Idefine_fun c = (ICommand.Idefine_fun)cmd;
            validateUserId(smtConfig, c.symbol(), errors);
            if (errors.isEmpty()) validateUniqueDeclarations(smtConfig, c.parameters(), errors);
        } else if (cmd instanceof ICommand.Idefine_funs_rec) {
            requireVersion(smtConfig, SMT.Configuration.SMTLIB.V25, "define-funs-rec", errors);
            ICommand.Idefine_funs_rec c = (ICommand.Idefine_funs_rec)cmd;
            if (c.declarations().size() != c.bodies().size())
                errors.add(smtConfig.responseFactory.error(
                    "The number of function declarations (" + c.declarations().size() +
                    ") must equal the number of bodies (" + c.bodies().size() + ")", null));
            for (IExpr.IFunctionDeclaration d : c.declarations()) {
                if (!errors.isEmpty()) break;
                validateUniqueDeclarations(smtConfig, d.parameters(), errors);
            }
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
        } else if (cmd instanceof ICommand.Iset_info || cmd instanceof ICommand.Iset_option) {
            // A symbol attribute value must be a legal symbol (the parser reports a reserved word in text)
            IKeyword k = cmd instanceof ICommand.Iset_info ? ((ICommand.Iset_info)cmd).infoflag()
                    : ((ICommand.Iset_option)cmd).option();
            IAttributeValue v = cmd instanceof ICommand.Iset_info ? ((ICommand.Iset_info)cmd).value()
                    : ((ICommand.Iset_option)cmd).value();
            IResponse keyErr = keywordError(smtConfig, k);
            if (keyErr != null) errors.add(keyErr);
            else if (v instanceof ISymbol) badSymbol(smtConfig, (ISymbol)v, errors);
        } else if (cmd instanceof ICommand.Iget_info || cmd instanceof ICommand.Iget_option) {
            IKeyword k = cmd instanceof ICommand.Iget_info ? ((ICommand.Iget_info)cmd).infoflag()
                    : ((ICommand.Iget_option)cmd).option();
            IResponse keyErr = keywordError(smtConfig, k);
            if (keyErr != null) errors.add(keyErr);
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
        else badSymbol(smtConfig, id, errors);
    }

    private static void validateUniqueDeclarations(SMT.Configuration smtConfig,
            List<IExpr.IDeclaration> params, List<IResponse> errors) {
        Set<ISymbol> seen = new HashSet<>();
        for (IExpr.IDeclaration d : params) {
            if (badSymbol(smtConfig, d.parameter(), errors)) return;
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
            if (badSymbol(smtConfig, p.symbol(), errors)) return;
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
                    if (badSymbol(smtConfig, p, errors)) return;
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
                if (badSymbol(smtConfig, ctor.symbol(), errors)) return;
                for (IExpr.ISelector sel : ctor.selectors()) {
                    if (badSymbol(smtConfig, sel.symbol(), errors)) return;
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

        for (IExpr.ISortDeclaration sd : sortDecls) {
            String name = sd.symbol().value();
            if (!wellFounded.contains(name)) {
                errors.add(smtConfig.responseFactory.error(
                    "Datatype " + name + " is not well-founded (no finite base case)", sd.symbol().pos()));
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
            if (datatypes.get(i).symbols() != null) {
                TypeChecker f = new TypeChecker(symTable);
                for (ISymbol p : datatypes.get(i).symbols()) {
                    if (f.shadowsLogic(p, true)) return f.result;
                }
            }
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
        /** Whether a reference to this variable is itself closed (no free/bound variable
         *  reachable through it) -- false for a quantifier- or match-pattern-bound
         *  variable (which IS the free variable), true for a let-bound variable whose own
         *  defining expression was itself closed when the let was checked, false for one
         *  that wasn't (e.g. {@code (forall ((q Bool)) (let ((r q)) ...))}: referencing
         *  {@code r} is not closed, because {@code r}'s value is the outer free {@code
         *  q}). See visit(ISymbol)/visit(ILet). */
        public boolean closed;
        public Variable(ISymbol sym, ISort sort, IExpr expr, boolean closed) {
            this.symbol = sym;
            this.sort = sort;
            this.expression = expr;
            this.closed = closed;
        }
    }

}