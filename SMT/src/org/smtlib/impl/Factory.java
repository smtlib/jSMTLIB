/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.impl;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import org.smtlib.*;
import org.smtlib.ICommand.IScript;
import org.smtlib.IExpr.*;
import org.smtlib.command.*;
import org.smtlib.IPos.IPosable;
import org.smtlib.ISort.IApplication;
import org.smtlib.ISort.IParameter;
import org.smtlib.impl.SMTExpr.*;
import org.smtlib.impl.Sort.*;
import org.smtlib.sexpr.Utils;

// FIXME - spearate out the concrete syntax?

/** Implements a factory for SMT-LIB expressions using the standard concrete syntax.
 * Instances of these IExpr objects have an IPos element. 
 * The various factories are all implemented together in this one class because they
 * use each other mutually; combining them lets them be overridden in a consistent fashion. */
public class Factory implements IExpr.IFactory, ISort.IFactory, ICommand.IFactory {
	
	/** Initializes the SMT configuration object for the implementation 
	 * in org.smtlib.impl - all the appropriate factories, etc.
	 * @param config the configuration object to initialize
	 */
	public static void initFactories(SMT.Configuration config) {
		config.responseFactory = new Response.Factory(config);
		Factory f = new Factory();
		config.sortFactory = f;
		config.exprFactory = f;
		config.commandFactory = f;
		config.utils = new Utils(config);
		config.reservedWords.addAll(Utils.reservedWords);
		config.reservedWordsNotCommands.addAll(Utils.reservedWordsNotCommands);
	}
	
	/** Sets the text position for a given instance. This is a template so it can return its
	 * receiver object without the type changing. */
	<T extends IPosable> T setPos(/*@Nullable*//*@ReadOnly*/IPos pos, T t) { t.setPos(pos); return t; }
	
	// The following methods are those of the Sort factory

	@Override
	public Family createSortFamily(IIdentifier identifier, INumeral arity) {
		return new Family(identifier,arity);
	}

	@Override
	public Parameter createSortParameter(ISymbol symbol) {
		return new Parameter(symbol);
	}

	// CAUTION: keeps a reference to the list of ISort parameters
	@Override
	public Application createSortExpression(IIdentifier sortFamily,
			List<ISort> exprs) {
		return new Application(sortFamily,exprs);
	}

	@Override
	public Application createSortExpression(IIdentifier sortFamily,
			ISort... exprs) {
		return new Application(sortFamily, Arrays.asList(exprs));
	}

	@Override
	public Abbreviation createSortAbbreviation(IIdentifier identifier,
			List<IParameter> params, ISort sortExpr) {
		return new Abbreviation(identifier,params,sortExpr);
	}

	@Override
	public FcnSort createFcnSort(ISort[] args, ISort result) {
		return new FcnSort(args,result);
	}

	@Override
	public ISort.IErrorDefinition createErrorDefinition(IIdentifier id, String errorMessage, IPos pos) {
		return new Sort.ErrorDefinition(id, errorMessage, pos);
	}

	@Override
	public IApplication Bool() {
		return Sort.Bool();
	}
	
	// The following methods implement ICommand.IFactory

	@Override
	public IScript script(/*@Nullable*/IStringLiteral filename, /*@Nullable*/List<ICommand> commands) {
		return new Script(filename,commands);
	}

	@Override public ICommand.Iassert            assertCommand(IExpr expr)                                                               { return new C_assert(expr); }
	@Override public ICommand.Icheck_sat         check_sat()                                                                             { return new C_check_sat(); }
	@Override public ICommand.Icheck_sat_assuming check_sat_assuming(List<IExpr> terms)                                                  { return new C_check_sat_assuming(terms); }
	@Override public ICommand.Ideclare_const     declare_const(ISymbol s, ISort r)                                                      { return new C_declare_const(s, r); }
	@Override public ICommand.Ideclare_datatype  declare_datatype(IExpr.ISortDeclaration sd, ISort.IDatatype d)                         { return new C_declare_datatype(sd, d); }
	@Override public ICommand.Ideclare_datatypes declare_datatypes(List<IExpr.ISortDeclaration> sds, List<ISort.IDatatype> dts)          { return new C_declare_datatypes(sds, dts); }
	@Override public ICommand.Ideclare_fun       declare_fun(ISymbol id, List<ISort> args, ISort r)                                     { return new C_declare_fun(id, args, r); }
	@Override public ICommand.Ideclare_sort      declare_sort(ISymbol s, INumeral n)                                                    { return new C_declare_sort(s, n); }
	@Override public ICommand.Ideclare_sort_parameter declare_sort_parameter(ISymbol s)                                                 { return new C_declare_sort_parameter(s); }
	@Override public ICommand.Idefine_const      define_const(ISymbol s, ISort r, IExpr e)                                             { return new C_define_const(s, r, e); }
	@Override public ICommand.Idefine_fun        define_fun(ISymbol id, List<IDeclaration> ps, ISort r, IExpr e)                       { return new C_define_fun(id, ps, r, e); }
	@Override public ICommand.Idefine_fun_rec    define_fun_rec(ISymbol id, List<IDeclaration> ps, ISort r, IExpr e)                   { return new C_define_fun_rec(id, ps, r, e); }
	@Override public ICommand.Idefine_funs_rec   define_funs_rec(List<IExpr.IFunctionDeclaration> ds, List<IExpr> bs)                  { return new C_define_funs_rec(ds, bs); }
	@Override public ICommand.Idefine_sort       define_sort(ISymbol id, List<IParameter> ps, ISort e)                                 { return new C_define_sort(id, ps, e); }
	@Override public ICommand.Iecho              echo(IStringLiteral arg)                                                               { return new C_echo(arg); }
	@Override public ICommand.Iexit              exit()                                                                                 { return new C_exit(); }
	@Override public ICommand.Iget_assertions    get_assertions()                                                                       { return new C_get_assertions(); }
	@Override public ICommand.Iget_assignment    get_assignment()                                                                       { return new C_get_assignment(); }
	@Override public ICommand.Iget_info          get_info(IKeyword k)                                                                   { return new C_get_info(k); }
	@Override public ICommand.Iget_model         get_model()                                                                            { return new C_get_model(); }
	@Override public ICommand.Iget_option        get_option(IKeyword k)                                                                 { return new C_get_option(k); }
	@Override public ICommand.Iget_proof         get_proof()                                                                            { return new C_get_proof(); }
	@Override public ICommand.Iget_unsat_assumptions get_unsat_assumptions()                                                            { return new C_get_unsat_assumptions(); }
	@Override public ICommand.Iget_unsat_core    get_unsat_core()                                                                       { return new C_get_unsat_core(); }
	@Override public ICommand.Iget_value         get_value(List<IExpr> exprs)                                                          { return new C_get_value(exprs); }
	@Override public ICommand.Ipush              push(INumeral n)                                                                       { return new C_push(n); }
	@Override public ICommand.Ipop               pop(INumeral n)                                                                        { return new C_pop(n); }
	@Override public ICommand.Ireset             reset()                                                                                { return new C_reset(); }
	@Override public ICommand.Ireset_assertions  reset_assertions()                                                                     { return new C_reset_assertions(); }
	@Override public ICommand.Iset_logic         set_logic(ISymbol s)                                                                  { return new C_set_logic(s); }
	@Override public ICommand.Iset_info          set_info(IKeyword k, IAttributeValue v)                                              { return new C_set_info(k, v); }
	@Override public ICommand.Iset_option        set_option(IKeyword k, IAttributeValue v)                                            { return new C_set_option(k, v); }

	// The following methods are those of the IExpr factory

	@Override
	public INumeral numeral(String v) {
		return new Numeral(new BigInteger(v));
	}

	@Override
	public Numeral numeral(long v) {
		return setPos(null,new Numeral(BigInteger.valueOf(v)));
	}

	@Override
	public IDecimal decimal(String v) {
		return new Decimal(new BigDecimal(v));
	}

	@Override
	public IStringLiteral unquotedString(String v) {
		return new StringLiteral(v,false);
	}

	@Override
	public IStringLiteral quotedString(String v) {
		return new StringLiteral(v,true);
	}

	@Override
	public IKeyword keyword(String v) {
		return new Keyword(v);
	}

	@Override
	public IBinaryLiteral binary(String v) {
		return new BinaryLiteral(v);
	}

	@Override
	public IHexLiteral hex(String v) {
		return new HexLiteral(v);
	}

	@Override
	public ISymbol symbol(String v) {
		return new Symbol(v);
	}

	@Override
	public IAttribute<?> attribute(IKeyword k) {
		return new Attribute<ILiteral>(k,null); // Just using ILiteral because we have to use some type
	}

	@Override
	public <T extends IAttributeValue> IAttribute<T> attribute(IKeyword k, T value) {
		return new Attribute<T>(k,value);
	}

	@Override
	public IAttributedExpr attributedExpr(IExpr e,
			List<IAttribute<?>> attributes) {
		return new AttributedExpr(e,attributes);
	}
	
	static class AttributeList<T> implements IAttributeValue {
	    public List<T> list;
	    public AttributeList(List<T> list) {this.list = list; }
        public IPos pos() { return null; }
        public void setPos(IPos p) {  }
        @Override
        public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }

        // For debugging only
        @Override
        public String toString() {
            String s = "(" ;
            for (T t: list) s = s + " " + t.toString();
            return s + " )";
        }

	}

	@Override
	public <T extends IAttributeValue> IAttributedExpr attributedExpr(IExpr e,
			IKeyword key, T value) {
		IAttribute<T> a = attribute(key,value);
		List<IAttribute<?>> list = new LinkedList<IAttribute<?>>();
		list.add(a);
		return new AttributedExpr(e,list);
	}

	@Override
	public IFcnExpr fcn(IQualifiedIdentifier id, List<IExpr> args) {
		List<IExpr> arglist = new LinkedList<IExpr>();
		for (IExpr a: args) arglist.add(a);
		return new FcnExpr(id,arglist);
	}

	@Override
    public IFcnExpr fcn(IQualifiedIdentifier id, IExpr... args) {
		List<IExpr> arglist = new LinkedList<IExpr>();
		for (IExpr a: args) arglist.add(a);
		return new FcnExpr(id,arglist);
	}

	@Override
	public IParameterizedIdentifier id(ISymbol symbol, List<IIndex> indices) {
		return new ParameterizedIdentifier(symbol, indices);
	}

	@Override
	public IAsIdentifier id(IIdentifier identifier, ISort qualifier) {
		return new AsIdentifier(identifier,qualifier);
	}

	@Override
	public ILet let(List<IBinding> bindings, IExpr e) {
		return new Let(bindings,e);
	}

	@Override
	public IBinding binding(ISymbol symbol, IExpr expr) {
		return new Binding(symbol,expr);
	}

	@Override
	public IDeclaration declaration(org.smtlib.IExpr.ISymbol symbol,
			ISort sort) {
		return new Declaration(symbol,sort);
	}
	
    @Override
    public IForall forall(List<IDeclaration> params, IExpr e) {
        return new Forall(params,e);
    }

    @Override
    public IForall forall(List<IDeclaration> params, IExpr e, List<IExpr> patterns) {
        if (patterns != null) {
            List<IAttribute<?>> attributes = new LinkedList<>();
            for (IExpr p: patterns) {
                attributes.add(attribute(keyword(":pattern"),p));
            }
            e = attributedExpr(e, attributes);
        }
        return new Forall(params,e);
    }

    @Override
    public IExists exists(List<IDeclaration> params, IExpr e) {
        return new Exists(params,e);
    }

    @Override
    public IExists exists(List<IDeclaration> params, IExpr e, List<IExpr> patterns) {
        if (patterns != null) {
            List<IAttribute<?>> attributes = new LinkedList<>();
            for (IExpr p: patterns) {
                attributes.add(attribute(keyword(":pattern"),p));
            }
            e = attributedExpr(e, attributes);
        }
        return new Exists(params,e);
    }

	@Override
	public IError error(String text) {
		return new SMTExpr.Error(text);
	}

	@Override
	public ISortDeclaration sortDeclaration(ISymbol symbol, INumeral arity) {
		return new SMTExpr.SortDeclaration(symbol, arity);
	}

	@Override
	public ISelector selector(ISymbol symbol, ISort sort) {
		return new SMTExpr.Selector(symbol, sort);
	}

	@Override
	public IConstructor constructor(ISymbol symbol, List<ISelector> selectors) {
		return new SMTExpr.Constructor(symbol, selectors);
	}

	@Override
	public ISort.IDatatype datatype(List<IConstructor> constructors, List<ISymbol> symbols) {
		return new SMTExpr.Datatype(constructors, symbols);
	}

	@Override
	public IFunctionDeclaration functionDeclaration(ISymbol symbol, List<IDeclaration> parameters, ISort sort) {
		return new SMTExpr.FunctionDeclaration(symbol, parameters, sort);
	}

	@Override
	public IExpr.IPattern pattern(IExpr.ISymbol constructor, List<IExpr.ISymbol> params) {
		return new SMTExpr.Pattern(constructor, params);
	}

	@Override
	public IExpr.IMatchCase matchCase(IExpr.IPattern pattern, IExpr body) {
		return new SMTExpr.MatchCase(pattern, body);
	}

	@Override
	public IExpr.IMatch match(IExpr expr, List<IExpr.IMatchCase> cases) {
		return new SMTExpr.Match(expr, cases);
	}

}
