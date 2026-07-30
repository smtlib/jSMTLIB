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
		/** Creates a script object containing the given filename or the given set of commands */
		IScript script(/*@Nullable*/IStringLiteral filename, /*@Nullable*/List<ICommand> commands);
		
		/** Creates an assert command object, asserting the given expression */
		Iassert assertCommand(IExpr expr);
		
        /** Creates a check-sat command object */
        Icheck_sat check_sat();
        
        /** Creates a check-sat-assuming command object */
        Icheck_sat_assuming check_sat_assuming(List<IExpr> terms);

        /** Creates a declare-const command object */
        Ideclare_const declare_const(ISymbol symbol, ISort resultSort);

		/** Creates a declare-fun command object */
		Ideclare_fun declare_fun(ISymbol id, List<ISort> argSorts, ISort resultSort);

        /** Creates a declare-sort command object. */
        Ideclare_sort declare_sort(ISymbol sym, INumeral arity);

        /** Creates a declare-sort-parameter command object. */
        Ideclare_sort_parameter declare_sort_parameter(ISymbol sym);

        /** Creates a declare-datatype command object */
        Ideclare_datatype declare_datatype(IExpr.ISortDeclaration sd, ISort.IDatatype d);

        /** Creates a declare-datatypes command object */
        Ideclare_datatypes declare_datatypes(List<IExpr.ISortDeclaration> sds, List<ISort.IDatatype> dts);

        /** Creates a define-const command object */
        Idefine_const define_const(ISymbol symbol, ISort resultSort, IExpr expression);

        /** Creates a define-fun command object */
        Idefine_fun define_fun(ISymbol id, List<IDeclaration> declarations, ISort resultSort, IExpr expression);

        /** Creates a define-fun-rec command object */
        Idefine_fun_rec define_fun_rec(ISymbol id, List<IDeclaration> declarations, ISort resultSort, IExpr expression);

        /** Creates a define-funs-rec command object */
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
		
		/** Creates a get-option command object */
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
        
		/** Creates a set-logic command object */
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
	
	/** Interface to be implemented by all objects representing SMT-LIB assert commands. */
	static public interface Iassert extends ICommand {
		IExpr expr();
	}
	
	/** Interface to be implemented by all objects representing SMT-LIB check-sat commands. */
	static public interface Icheck_sat extends ICommand {
	}
	
	/** Interface to be implemented by all objects representing SMT-LIB check-sat-assuming commands. */
	static public interface Icheck_sat_assuming extends ICommand {
        List<IExpr> exprs();
	}
	
    /** Interface to be implemented by all objects representing SMT-LIB declare-const commands. */
    static public interface Ideclare_const extends ICommand {
        ISymbol symbol();
        ISort resultSort();
        // FIXME;
    }
    
    /** Interface for the declare-datatypes command: a list of sort declarations and parallel datatype declarations. */
    static public interface Ideclare_datatypes extends ICommand {
        List<IExpr.ISortDeclaration> sortDeclarations();
        List<ISort.IDatatype> datatypes();
    }

    /** Interface for the declare-datatype command: a sort declaration and its datatype body. */
    static public interface Ideclare_datatype extends ICommand {
        IExpr.ISortDeclaration sortDeclaration();
        ISort.IDatatype datatype();
    }
    
	/** Interface to be implemented by all objects representing SMT-LIB declare-fun commands. */
	static public interface Ideclare_fun extends ICommand {
		ISymbol symbol();
		List<ISort> argSorts();
		ISort resultSort();
	}
	
    /** Interface to be implemented by all objects representing SMT-LIB declare-sort commands. */
    static public interface Ideclare_sort extends ICommand {
        ISymbol sortSymbol();
        INumeral arity();
    }
    
    /** Interface to be implemented by all objects representing SMT-LIB declare-sort commands. */
    static public interface Ideclare_sort_parameter extends ICommand {
        ISymbol sortSymbol();
    }
    
    /** Interface to be implemented by all objects representing SMT-LIB define-const commands. */
    static public interface Idefine_const extends ICommand {
        ISymbol symbol();
        ISort resultSort();
        IExpr expression();
    }
    
    /** Interface to be implemented by all objects representing SMT-LIB define-fun commands. */
    static public interface Idefine_fun extends ICommand {
        ISymbol symbol();
        List<IDeclaration> parameters();
        ISort resultSort();
        IExpr expression();
    }
    
    /** Interface to be implemented by all objects representing SMT-LIB define-fun-rec commands. */
    static public interface Idefine_fun_rec extends ICommand {
        ISymbol symbol();
        List<IDeclaration> parameters();
        ISort resultSort();
        IExpr expression();
    }
    
    /** Interface to be implemented by all objects representing SMT-LIB define-funs-rec commands. */
    static public interface Idefine_funs_rec extends ICommand {
        List<IExpr.IFunctionDeclaration> declarations();
        List<IExpr> bodies();
    }
    
	/** Interface to be implemented by all objects representing SMT-LIB define-sort commands. */
	static public interface Idefine_sort extends ICommand {
		ISymbol sortSymbol();
		List<IParameter> parameters();
		ISort expression();
	}
	
    /** Interface to be implemented by all objects representing SMT-LIB exit commands. */
    static public interface Iecho extends ICommand {
        IStringLiteral arg();
    }
    
    /** Interface to be implemented by all objects representing SMT-LIB exit commands. */
    static public interface Iexit extends ICommand {
    }
    
	/** Interface to be implemented by all objects representing SMT-LIB get-assertions commands. */
	static public interface Iget_assertions extends ICommand {
	}
	
	/** Interface to be implemented by all objects representing SMT-LIB get-assignment commands. */
	static public interface Iget_assignment extends ICommand {
	}
	
	/** Interface to be implemented by all objects representing SMT-LIB get-info commands. */
	static public interface Iget_info extends ICommand {
		IKeyword infoflag();
	}
	
	/** Interface to be implemented by all objects representing SMT-LIB get-option commands. */
	static public interface Iget_option extends ICommand {
		IKeyword option();
	}
	
	/** Interface to be implemented by all objects representing SMT-LIB get-model commands (non-standard). */
	static public interface Iget_model extends ICommand {
	}

	/** Interface to be implemented by all objects representing SMT-LIB get-proof commands. */
	static public interface Iget_proof extends ICommand {
	}
	
	/** Interface to be implemented by all objects representing SMT-LIB get-unsat-assumptions commands. */
	static public interface Iget_unsat_assumptions extends ICommand {
	}

	/** Interface to be implemented by all objects representing SMT-LIB get-unsat-core commands. */
	static public interface Iget_unsat_core extends ICommand {
	}

	/** Interface to be implemented by all objects representing SMT-LIB get-value commands. */
	static public interface Iget_value extends ICommand {
		//@ ensures exprs().size > 0;
		List<IExpr> exprs();
	}
	
	/** Interface to be implemented by all objects representing SMT-LIB pop commands. */
	static public interface Ipop extends ICommand {
		//@ ensures \result.intValue() >= 0;
		INumeral number();
	}
	
	/** Interface to be implemented by all objects representing SMT-LIB push commands. */
	static public interface Ipush extends ICommand {
		//@ ensures \result.intValue() >= 0;
		INumeral number();
	}
	
	/** Interface to be implemented by all objects representing SMT-LIB reset commands. */
	static public interface Ireset extends ICommand {
	}
	
	/** Interface to be implemented by all objects representing SMT-LIB reset-assertions commands. */
	static public interface Ireset_assertions extends ICommand {
	}
	
	/** Interface to be implemented by all objects representing SMT-LIB set-logic commands. */
	static public interface Iset_logic extends ICommand {
		ISymbol logic();
	}
	
	/** Interface to be implemented by all objects representing SMT-LIB set-info commands. */
	static public interface Iset_info extends ICommand {
		IKeyword infoflag();
		IAttributeValue value();
	}
	
	/** Interface to be implemented by all objects representing SMT-LIB set-option commands. */
	static public interface Iset_option extends ICommand {
		IKeyword option();
		/*@Nullable*/IAttributeValue value();
	}
}
