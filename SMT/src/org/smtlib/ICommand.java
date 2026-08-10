/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib;

import java.util.List;

import org.smtlib.IExpr.IDeclaration;
import org.smtlib.IExpr.IIdentifier;
import org.smtlib.IExpr.IKeyword;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IExpr.IStringLiteral;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.ISort.IParameter;


/** This interface is the generic interface to command classes, providing functionality
 * to type-check the command and to execute it.
 * @author David R. Cok
 */
public interface ICommand extends INode {
	
	/** This interface defines classes that implement techniques for mapping a command name to a class
	 * that implements that command.
	 */
	public static interface IFinder {
		/** This method finds a class that implements the ICommand interface for the given class name */
		Class<? extends ICommand> findCommand(String name);
	}
	
	/** Returns the SMT-LIB name of this command (e.g. {@code "assert"}, {@code "check-sat"}). */
	String commandName();

	/** Executes the command on the given solver; presumes that the command type-checked
	 * successfully.
	 * @param solver the instance of the solver to use (note that solvers have state)
	 * @return the result of the command
	 */
	IResponse execute(ISolver solver);
	
	/** This is the interface to be used by a concrete ICommand factory. */
	static public interface IFactory {
		/** Creates a script object containing the given filename or the given set of commands. */
		IScript script(/*@Nullable*/IStringLiteral filename, /*@Nullable*/List<ICommand> commands);

		/** Creates an assert command object, asserting the given expression. */
		Iassert assertCommand(IExpr expr);

        /** Creates a check-sat command object. */
        Icheck_sat check_sat();

        /** Creates a check-sat-assuming command object. */
        Icheck_sat_assuming check_sat_assuming(List<IExpr> terms);

        /** Creates a declare-const command object. */
        Ideclare_const declare_const(ISymbol symbol, ISort resultSort);

		/** Creates a declare-fun command object. */
		Ideclare_fun declare_fun(ISymbol id, List<ISort> argSorts, ISort resultSort);

        /** Creates a declare-sort command object. */
        Ideclare_sort declare_sort(ISymbol sym, INumeral arity);

        /** Creates a declare-sort-parameter command object. */
        Ideclare_sort_parameter declare_sort_parameter(ISymbol sym);

        /** Creates a declare-datatype command object. */
        Ideclare_datatype declare_datatype(IExpr.ISortDeclaration sd, ISort.IDatatype d);

        /** Creates a declare-datatypes command object. */
        Ideclare_datatypes declare_datatypes(List<IExpr.ISortDeclaration> sds, List<ISort.IDatatype> dts);

        /** Creates a define-const command object. */
        Idefine_const define_const(ISymbol symbol, ISort resultSort, IExpr expression);

        /** Creates a define-fun command object. */
        Idefine_fun define_fun(ISymbol id, List<IDeclaration> declarations, ISort resultSort, IExpr expression);

        /** Creates a define-fun-rec command object. */
        Idefine_fun_rec define_fun_rec(ISymbol id, List<IDeclaration> declarations, ISort resultSort, IExpr expression);

        /** Creates a define-funs-rec command object. */
        Idefine_funs_rec define_funs_rec(List<IExpr.IFunctionDeclaration> declarations, List<IExpr> bodies);

		/** Creates a define-sort command object. */
		Idefine_sort define_sort(ISymbol id, List<IParameter> parameters, ISort expression);

        /** Creates an echo command object. */
        Iecho echo(IStringLiteral arg);

        /** Creates an exit command object. */
        Iexit exit();
        
		/** Creates a get-assertions command object. */
		Iget_assertions get_assertions();
		
		/** Creates a get-assignment command object. */
		Iget_assignment get_assignment();
		
		/** Creates a get-info command object. */
		Iget_info get_info(IKeyword infoflag);
		
		/** Creates a get-option command object. */
		Iget_option get_option(IKeyword option);
		
		/** Creates a get-model command object. */
		Iget_model get_model();

		/** Creates a get-proof command object. */
		Iget_proof get_proof();

        /** Creates a get-unsat-assumptions command object. */
        Iget_unsat_assumptions get_unsat_assumptions();
        
        /** Creates a get-unsat-core command object. */
        Iget_unsat_core get_unsat_core();
        
		/** Creates a get-value command object. */
		Iget_value get_value(List<IExpr> exprs);
		
		/** Creates a push command object. */
		Ipush push(INumeral number);
		
        /** Creates a pop command object. */
        Ipop pop(INumeral number);
        
        /** Creates a reset command object. */
        Ireset reset();
        
        /** Creates a reset-assertions command object. */
        Ireset_assertions reset_assertions();
        
		/** Creates a set-logic command object. */
		Iset_logic set_logic(ISymbol logic);
		
		/** Creates a set-info command object. */
		Iset_info set_info(IKeyword infoflag, IAttributeValue value);
		
		/** Creates a set-option command object. */
		Iset_option set_option(IKeyword option, IAttributeValue value);
	}
	
	/** Interface to be implemented by all objects representing SMT-LIB scripts. A script may consist of a file or an explicit list of commands. */
	// FIXME - move to org.smtlib?
	static public interface IScript extends INode {
		/*@Nullable*/ IStringLiteral filename();
		/*@Nullable*/ List<ICommand> commands();
		IResponse execute(ISolver solver);
	}
	
	/** Interface for the SMT-LIB {@code assert} command. */
	static public interface Iassert extends ICommand {
		/** Returns the expression to be asserted. */
		IExpr expr();
	}

	/** Interface for the SMT-LIB {@code check-sat} command. */
	static public interface Icheck_sat extends ICommand {
	}

	/** Interface for the SMT-LIB {@code check-sat-assuming} command. */
	static public interface Icheck_sat_assuming extends ICommand {
		/** Returns the boolean-sorted terms to assume. */
        List<IExpr> terms();
	}

	/** Interface for the SMT-LIB {@code declare-const} command. */
    static public interface Ideclare_const extends ICommand {
    	/** Returns the name of the constant being declared. */
        ISymbol symbol();
        /** Returns the sort of the constant being declared. */
        ISort resultSort();
    }

	/** Interface for the SMT-LIB {@code declare-datatypes} command. */
    static public interface Ideclare_datatypes extends ICommand {
    	/** Returns the list of sort declarations (names and arities). */
        List<IExpr.ISortDeclaration> sortDeclarations();
        /** Returns the list of datatype bodies, parallel to {@link #sortDeclarations()}. */
        List<ISort.IDatatype> datatypes();
    }

	/** Interface for the SMT-LIB {@code declare-datatype} command. */
    static public interface Ideclare_datatype extends ICommand {
    	/** Returns the sort declaration (name and arity). */
        IExpr.ISortDeclaration sortDeclaration();
        /** Returns the datatype body. */
        ISort.IDatatype datatype();
    }

	/** Interface for the SMT-LIB {@code declare-fun} command. */
	static public interface Ideclare_fun extends ICommand {
		/** Returns the name of the function being declared. */
		ISymbol symbol();
		/** Returns the list of argument sorts. */
		List<ISort> argSorts();
		/** Returns the result sort. */
		ISort resultSort();
	}

	/** Interface for the SMT-LIB {@code declare-sort} command. */
    static public interface Ideclare_sort extends ICommand {
    	/** Returns the name of the sort being declared. */
        ISymbol sortSymbol();
        /** Returns the arity of the sort. */
        INumeral arity();
    }

	/** Interface for the SMT-LIB {@code declare-sort-parameter} command. */
    static public interface Ideclare_sort_parameter extends ICommand {
    	/** Returns the name of the sort parameter being declared. */
        ISymbol sortSymbol();
    }

	/** Interface for the SMT-LIB {@code define-const} command.
	 *  Syntactic sugar for {@code define-fun} with an empty parameter list. */
    static public interface Idefine_const extends Idefine_fun {
    }

	/** Interface for the SMT-LIB {@code define-fun} command. */
    static public interface Idefine_fun extends ICommand {
    	/** Returns the name of the function being defined. */
        ISymbol symbol();
        /** Returns the list of formal parameters. */
        List<IDeclaration> parameters();
        /** Returns the result sort. */
        ISort resultSort();
        /** Returns the defining expression (body). */
        IExpr expression();
    }

	/** Interface for the SMT-LIB {@code define-fun-rec} command. */
    static public interface Idefine_fun_rec extends ICommand {
    	/** Returns the name of the function being defined. */
        ISymbol symbol();
        /** Returns the list of formal parameters. */
        List<IDeclaration> parameters();
        /** Returns the result sort. */
        ISort resultSort();
        /** Returns the defining expression (body). */
        IExpr expression();
    }

	/** Interface for the SMT-LIB {@code define-funs-rec} command. */
    static public interface Idefine_funs_rec extends ICommand {
    	/** Returns the list of function declarations. */
        List<IExpr.IFunctionDeclaration> declarations();
        /** Returns the list of defining expressions (bodies), parallel to {@link #declarations()}. */
        List<IExpr> bodies();
    }

	/** Interface for the SMT-LIB {@code define-sort} command. */
	static public interface Idefine_sort extends ICommand {
		/** Returns the name of the sort being defined. */
		ISymbol sortSymbol();
		/** Returns the list of sort parameters. */
		List<IParameter> parameters();
		/** Returns the sort expression that is the definition. */
		ISort expression();
	}

	/** Interface for the SMT-LIB {@code echo} command. */
    static public interface Iecho extends ICommand {
    	/** Returns the string literal to be echoed. */
        IStringLiteral arg();
    }

	/** Interface for the SMT-LIB {@code exit} command. */
    static public interface Iexit extends ICommand {
    }

	/** Interface for the SMT-LIB {@code get-assertions} command. */
	static public interface Iget_assertions extends ICommand {
	}

	/** Interface for the SMT-LIB {@code get-assignment} command. */
	static public interface Iget_assignment extends ICommand {
	}

	/** Interface for the SMT-LIB {@code get-info} command. */
	static public interface Iget_info extends ICommand {
		/** Returns the info flag keyword being queried. */
		IKeyword infoflag();
	}

	/** Interface for the SMT-LIB {@code get-option} command. */
	static public interface Iget_option extends ICommand {
		/** Returns the option keyword being queried. */
		IKeyword option();
	}

	/** Interface for the SMT-LIB {@code get-model} command (non-standard extension). */
	static public interface Iget_model extends ICommand {
	}

	/** Interface for the SMT-LIB {@code get-proof} command. */
	static public interface Iget_proof extends ICommand {
	}

	/** Interface for the SMT-LIB {@code get-unsat-assumptions} command. */
	static public interface Iget_unsat_assumptions extends ICommand {
	}

	/** Interface for the SMT-LIB {@code get-unsat-core} command. */
	static public interface Iget_unsat_core extends ICommand {
	}

	/** Interface for the SMT-LIB {@code get-value} command. */
	static public interface Iget_value extends ICommand {
		//@ ensures exprs().size > 0;
		/** Returns the list of expressions whose values are requested. */
		List<IExpr> exprs();
	}

	/** Interface for the SMT-LIB {@code pop} command. */
	static public interface Ipop extends ICommand {
		//@ ensures \result.intValue() >= 0;
		/** Returns the number of scopes to pop. */
		INumeral number();
	}

	/** Interface for the SMT-LIB {@code push} command. */
	static public interface Ipush extends ICommand {
		//@ ensures \result.intValue() >= 0;
		/** Returns the number of scopes to push. */
		INumeral number();
	}

	/** Interface for the SMT-LIB {@code reset} command. */
	static public interface Ireset extends ICommand {
	}

	/** Interface for the SMT-LIB {@code reset-assertions} command. */
	static public interface Ireset_assertions extends ICommand {
	}

	/** Interface for the SMT-LIB {@code set-logic} command. */
	static public interface Iset_logic extends ICommand {
		/** Returns the logic name. */
		ISymbol logic();
	}

	/** Interface for the SMT-LIB {@code set-info} command. */
	static public interface Iset_info extends ICommand {
		/** Returns the info flag keyword. */
		IKeyword infoflag();
		/** Returns the attribute value. */
		IAttributeValue value();
	}

	/** Interface for the SMT-LIB {@code set-option} command. */
	static public interface Iset_option extends ICommand {
		/** Returns the option keyword. */
		IKeyword option();
		/** Returns the option value, or {@code null} if none was provided. */
		/*@Nullable*/IAttributeValue value();
	}
}
