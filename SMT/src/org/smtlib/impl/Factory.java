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
import org.smtlib.IExpr.IAsIdentifier;
import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.IAttributeValue;
import org.smtlib.IExpr.IAttributedExpr;
import org.smtlib.IExpr.IBinaryLiteral;
import org.smtlib.IExpr.IBinding;
import org.smtlib.IExpr.IDecimal;
import org.smtlib.IExpr.IDeclaration;
import org.smtlib.IExpr.IError;
import org.smtlib.IExpr.IExists;
import org.smtlib.IExpr.IFcnExpr;
import org.smtlib.IExpr.IForall;
import org.smtlib.IExpr.IHexLiteral;
import org.smtlib.IExpr.IIdentifier;
import org.smtlib.IExpr.IKeyword;
import org.smtlib.IExpr.ILet;
import org.smtlib.IExpr.ILiteral;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IExpr.IParameterizedIdentifier;
import org.smtlib.IExpr.IQualifiedIdentifier;
import org.smtlib.IExpr.IStringLiteral;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IExpr.ISymbol.ILetParameter;
import org.smtlib.IPos.IPosable;
import org.smtlib.ISort.IExpression;
import org.smtlib.ISort.IParameter;
import org.smtlib.impl.SMTExpr.AsIdentifier;
import org.smtlib.impl.SMTExpr.Attribute;
import org.smtlib.impl.SMTExpr.AttributedExpr;
import org.smtlib.impl.SMTExpr.BinaryLiteral;
import org.smtlib.impl.SMTExpr.Binding;
import org.smtlib.impl.SMTExpr.Decimal;
import org.smtlib.impl.SMTExpr.Declaration;
import org.smtlib.impl.SMTExpr.Exists;
import org.smtlib.impl.SMTExpr.FcnExpr;
import org.smtlib.impl.SMTExpr.Forall;
import org.smtlib.impl.SMTExpr.HexLiteral;
import org.smtlib.impl.SMTExpr.Keyword;
import org.smtlib.impl.SMTExpr.Let;
import org.smtlib.impl.SMTExpr.Numeral;
import org.smtlib.impl.SMTExpr.ParameterizedIdentifier;
import org.smtlib.impl.SMTExpr.StringLiteral;
import org.smtlib.impl.SMTExpr.Symbol;
import org.smtlib.impl.Sort.Abbreviation;
import org.smtlib.impl.Sort.Expression;
import org.smtlib.impl.Sort.Family;
import org.smtlib.impl.Sort.FcnSort;
import org.smtlib.impl.Sort.Parameter;
import org.smtlib.sexpr.Utils;

/** Implements a factory for SMT-LIB expressions using the standard concrete syntax.
 * Instances of these IExpr objects have an IPos element. 
 * The various factories are all implemented together in this one class because they
 * use each other mutually; combining them lets them be overridden in a consistent fashion. */
public class Factory implements IExpr.IFactory, ISort.IFactory {
	
	/** Initializes the SMT configuration object for the implementation 
	 * in org.smtlib.impl - all the appropriate factories, etc.
	 * @param config the configuration object to initialize
	 */
	public static void initFactories(SMT.Configuration config) {
		// FIXME - put everything into the Factory?
		config.responseFactory = new Response.Factory(config);
		Factory f = new Factory();
		config.sortFactory = f;
		config.exprFactory = f;
		config.utils = new Utils(config);
		config.reservedWords.addAll(Utils.reservedWords);
		config.reservedWordsNotCommands.addAll(Utils.reservedWordsNotCommands);
	}
	
	/** Sets the text position for a given instance. This is a template so it can return its
	 * receiver object without the type changing. */
	<T extends IPosable> T setPos(/*@Nullable*//*@ReadOnly*/IPos pos, T t) { t.setPos(pos); return t; }
	
	@Override
	public Numeral numeral(String v, /*@Nullable*//*@ReadOnly*/ IPos pos) {
		return setPos(pos,new Numeral(new BigInteger(v)));
	}

	@Override
	public Numeral numeral(long v) {
		return setPos(null,new Numeral(BigInteger.valueOf(v)));
	}

	@Override
	public Decimal decimal(String v, /*@Nullable*//*@ReadOnly*/ IPos pos) {
		return setPos(pos,new Decimal(new BigDecimal(v)));
	}

	@Override
	public StringLiteral quotedString(String v, /*@Nullable*//*@ReadOnly*/ IPos pos) {
		return setPos(pos,new StringLiteral(v,true));
	}

	@Override
	public StringLiteral unquotedString(String v, /*@Nullable*//*@ReadOnly*/ IPos pos) {
		return setPos(pos,new StringLiteral(v,false));
	}

	@Override
	public Keyword keyword(String v, /*@Nullable*//*@ReadOnly*/ IPos pos) {
		return setPos(pos,new Keyword(v));
	}

	@Override
	public BinaryLiteral binary(String v, /*@Nullable*//*@ReadOnly*/ IPos pos) {
		return setPos(pos,new BinaryLiteral(v));
	}

	@Override
	public HexLiteral hex(String v, /*@Nullable*//*@ReadOnly*/ IPos pos) {
		return setPos(pos,new HexLiteral(v));
	}

	@Override
	public Symbol symbol(String v, /*@Nullable*//*@ReadOnly*/ IPos pos) {
		return setPos(pos,new Symbol(v));
	}

	@Override
	public Attribute<?> attribute(IKeyword k, /*@Nullable*//*@ReadOnly*/ IPos pos) {
		Attribute<?> a = new Attribute<ILiteral>(k,null); // TODO: Just using ILiteral because we have to use some type
		a.setPos(pos);
		return a;
	}

	@Override
	public <T extends IAttributeValue> Attribute<T> attribute(IKeyword k, T value, /*@Nullable*//*@ReadOnly*/ IPos pos) {
		Attribute<T> a = new Attribute<T>(k,value);
		a.setPos(pos);
		return a;
	}

	@Override
	public AttributedExpr attributedExpr(IExpr e, List<IAttribute<?>> attr, /*@Nullable*//*@ReadOnly*/ IPos pos) {
		return setPos(pos,new AttributedExpr(e,attr));
	}

	@Override
	public <T extends IAttributeValue> AttributedExpr attributedExpr(IExpr e, IKeyword key, T value, /*@Nullable*//*@ReadOnly*/ IPos pos) {
		IAttribute<?> a = attribute(key,value,pos);
		List<IAttribute<?>> list = new LinkedList<IAttribute<?>>();
		list.add(a);
		return setPos(pos,new AttributedExpr(e,list));
	}

    @Override
    public FcnExpr fcn(IQualifiedIdentifier id, List<IExpr> args, /*@Nullable*//*@ReadOnly*/ IPos pos) {
        return setPos(pos,new FcnExpr(id,args));
    }

    @Override
    public FcnExpr fcn(IQualifiedIdentifier id, IExpr... args) {
        List<IExpr> arglist = new LinkedList<IExpr>();
        for (IExpr a: args) arglist.add(a);
        return new FcnExpr(id,arglist);
    }

	@Override
	public ParameterizedIdentifier id(ISymbol symbol, List<INumeral> nums, /*@Nullable*//*@ReadOnly*/ IPos pos) {
		return setPos(pos,new ParameterizedIdentifier(symbol,nums));
	}
	
	@Override
	public AsIdentifier id(IIdentifier identifier, ISort qualifier, /*@Nullable*//*@ReadOnly*/ IPos pos) {
		return setPos(pos,new AsIdentifier(identifier,qualifier));
	}
	
	@Override
	public Let let(List<IBinding> params, IExpr e, /*@Nullable*//*@ReadOnly*/ IPos pos) {
		return setPos(pos, new Let(params,e));
	}
	
	@Override
	public Declaration declaration(ISymbol.IParameter symbol, ISort sort, /*@Nullable*//*@ReadOnly*/ IPos pos) {
		return setPos(pos, new Declaration(symbol,sort));
	}

	@Override
	public Binding binding(ISymbol.ILetParameter symbol, IExpr expr, /*@Nullable*//*@ReadOnly*/ IPos pos) {
		return setPos(pos, new Binding(symbol,expr));
	}

	@Override
	public Forall forall(List<IDeclaration> params, IExpr e, /*@Nullable*//*@ReadOnly*/ IPos pos) {
		return setPos(pos, new Forall(params,e));
	}

	@Override
	public Exists exists(List<IDeclaration> params, IExpr e, /*@Nullable*//*@ReadOnly*/ IPos pos) {
		return setPos(pos, new Exists(params,e));
	}
	
	@Override
	public IScript script(/*@Nullable*/IStringLiteral filename, /*@Nullable*/List<ICommand> commands) {
		return new Command.Script(filename,commands);
	}


	@Override
	public SMTExpr.Error error(String text, /*@Nullable*//*@ReadOnly*/ IPos pos) {
		return setPos(pos,new SMTExpr.Error(text));
	}

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
	public Expression createSortExpression(IIdentifier sortFamily,
			List<ISort> exprs) {
		return new Expression(sortFamily,exprs);
	}

	// CAUTION: keeps a reference to the list of ISort expressions
	@Override
	public Expression createSortExpression(IIdentifier sortFamily,
			ISort... exprs) {
		return new Expression(sortFamily, Arrays.asList(exprs));
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
	public IExpression Bool() {
		IExpression sort = createSortExpression(symbol("Bool",null));
		return sort;
	}

	@Override
	public INumeral numeral(String v) {
		return numeral(v,null);
	}

	@Override
	public IDecimal decimal(String v) {
		return decimal(v,null);
	}

	@Override
	public IStringLiteral unquotedString(String v) {
		return unquotedString(v,null);
	}

	@Override
	public IStringLiteral quotedString(String v) {
		return quotedString(v,null);
	}

	@Override
	public IKeyword keyword(String v) {
		return keyword(v,null);
	}

	@Override
	public IBinaryLiteral binary(String v) {
		return binary(v,null);
	}

	@Override
	public IHexLiteral hex(String v) {
		return hex(v,null);
	}

	@Override
	public ISymbol symbol(String v) {
		return symbol(v,null);
	}

	@Override
	public IAttribute<?> attribute(IKeyword k) {
		return attribute(k,(IPos)null);
	}

	@Override
	public <T extends IAttributeValue> IAttribute<T> attribute(IKeyword k,
			T value) {
		return attribute(k,value,null);
	}

	@Override
	public IAttributedExpr attributedExpr(IExpr e,
			List<IAttribute<?>> attributes) {
		return attributedExpr(e,attributes,null);
	}

	@Override
	public <T extends IAttributeValue> IAttributedExpr attributedExpr(IExpr e,
			IKeyword key, T value) {
		return attributedExpr(e,key,value,null);
	}

	@Override
	public IFcnExpr fcn(IQualifiedIdentifier id, List<IExpr> args) {
		return fcn(id,args,null);
	}

	@Override
	public IParameterizedIdentifier id(ISymbol symbol, List<INumeral> num) {
		return id(symbol,num,null);
	}

	@Override
	public IAsIdentifier id(IIdentifier identifier, ISort qualifier) {
		return id(identifier,qualifier,null);
	}

	@Override
	public ILet let(List<IBinding> bindings, IExpr e) {
		return let(bindings,e,null);
	}

	@Override
	public IBinding binding(ILetParameter symbol, IExpr expr) {
		return binding(symbol,expr,null);
	}

	@Override
	public IDeclaration declaration(org.smtlib.IExpr.ISymbol.IParameter symbol,
			ISort sort) {
		return declaration(symbol,sort,null);
	}

	@Override
	public IForall forall(List<IDeclaration> params, IExpr e) {
		return forall(params,e,null);
	}

	@Override
	public IExists exists(List<IDeclaration> params, IExpr e) {
		return exists(params,e,null);
	}

	@Override
	public IError error(String text) {
		return error(text,null);
	}

}
