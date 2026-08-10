/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib;

import org.smtlib.ICommand.*;
import org.smtlib.IExpr.IKeyword;
import org.smtlib.IExpr.IStringLiteral;


/** This is the interface to be implemented by any solver adapter;
 * there is a method for each SMT-LIB command. */
public interface ISolver {

	/** Returns the configuration object with which the solver is initialized */
	SMT.Configuration smt();

	/** Returns the result of the most recent check-sat or check-sat-assuming, or null if none has been issued
	 * since the last push/pop/assert/declare/define. */
	/*@Nullable*/ IResponse checkSatStatus();

	/** A public, user-readable name for the solver adapter class */
	String solverName();

	/** Starts the solver; this is not an SMT-LIB command, but it is convenient in some implementations
	 * to separate the starting and initialization from the construction of the solver instance.
	 * @return success or an SMT error response
	 */
	IResponse start();

	/** Resets the solver to the initial state, clearing all assertions, declarations, and options.
	 * @return success or an SMT error response
	 */
	IResponse reset();

	/** Removes asserted formulae (but not global declarations when :global-declarations is true).
	 * @return success or an SMT error response
	 */
	IResponse reset_assertions();

	/** Terminates the solver; no further commands are permitted.
	 * @return success or an SMT error response
	 */
	IResponse exit();

	/** Terminates the solver forcibly without sending commands (e.g. by killing the process). */
	void forceExit();

	/** Echoes the argument string back to the output channel.
	 * @return the argument as an IResponse
	 */
	IResponse echo(IStringLiteral arg);

	/** Passes comment text to the solver (for logging/tracing); the argument is the comment body
	 * without the leading semicolon. */
	void comment(String comment);

	/** Sets the logic the solver should use.
	 * @param logicName the name of the logic
	 * @param pos source position used only for error messages; may be null
	 * @return success or unsupported or an SMT error response
	 */
	IResponse set_logic(String logicName, /*@Nullable*/ IPos pos);

	/** Adds the given number of empty assertion-stack frames to the solver state.
	 * @param number non-negative number of frames to push
	 * @return success or an SMT error response
	 */
	//@ requires number >= 0;
	IResponse push(int number);

	/** Removes the given number of assertion-stack frames from the solver state.
	 * @param number non-negative number of frames to pop
	 * @return success or an SMT error response
	 */
	//@ requires number >= 0;
	IResponse pop(int number);

	/** Adds the given expression to the current assertion-stack frame.
	 * The SMT-LIB command name is {@code assert}; the Java method name differs to avoid the Java reserved word.
	 * @return success or an SMT error response
	 */
	IResponse assertExpr(IExpr expr);

	/** Checks whether the current assertion set is satisfiable under the current logic.
	 * @return sat, unsat, unknown, or an SMT error response
	 */
	IResponse check_sat();

	/** Checks satisfiability under the current assertion set plus the given propositional assumptions.
	 * @return sat, unsat, unknown, or an SMT error response
	 */
	IResponse check_sat_assuming(IExpr... exprs);

	/** Declares a new uninterpreted constant; returns success or an SMT error response */
	IResponse declare_const(Ideclare_const cmd);

	/** Declares a new datatype sort; returns success or an SMT error response */
	IResponse declare_datatype(Ideclare_datatype cmd);

	/** Declares mutually recursive datatype sorts; returns success or an SMT error response */
	IResponse declare_datatypes(Ideclare_datatypes cmd);

	/** Declares a new uninterpreted function (or constant); returns success or an SMT error response */
	IResponse declare_fun(Ideclare_fun cmd);

	/** Declares a new uninterpreted sort; returns success or an SMT error response */
	IResponse declare_sort(Ideclare_sort cmd);

	/** Declares a new sort parameter (polymorphic sort variable); returns success or an SMT error response */
	IResponse declare_sort_parameter(Ideclare_sort_parameter cmd);

	/** Defines a named constant — syntactic sugar for {@code define-fun} with no parameters;
	 * returns success or an SMT error response */
	IResponse define_const(Idefine_const cmd);

	/** Defines a named function or constant; returns success or an SMT error response */
	IResponse define_fun(Idefine_fun cmd);

	/** Defines a named recursive function; returns success or an SMT error response */
	IResponse define_fun_rec(Idefine_fun_rec cmd);

	/** Defines a group of mutually recursive functions; returns success or an SMT error response */
	IResponse define_funs_rec(Idefine_funs_rec cmd);

	/** Defines a sort abbreviation; returns success or an SMT error response */
	IResponse define_sort(Idefine_sort cmd);

	/** Sets an SMT-LIB option.
	 * @param option the keyword naming the option
	 * @param value the value to set
	 * @return success, unsupported, or an SMT error response
	 */
	IResponse set_option(IKeyword option, IAttributeValue value);

	/** Annotates the problem with an info attribute (e.g. {@code :status sat}).
	 * @param key the info keyword
	 * @param value the attribute value
	 * @return success, unsupported, or an SMT error response
	 */
	IResponse set_info(IKeyword key, IAttributeValue value);

	/** Returns the list of formulae in the current assertion set, in the order they were asserted.
	 * Requires :produce-assertions to be enabled; returns an error if it is not.
	 * SMT-LIB does not stipulate the order of the terms in the returned list.
	 * @return a sequence of asserted terms, unsupported, or an SMT error response
	 */
	IResponse get_assertions();

	/** Returns a proof of unsatisfiability for the current assertion set.
	 * Requires :produce-proofs to be enabled; returns an error if it is not.
	 * @return a proof, unsupported, or an SMT error response
	 */
	IResponse get_proof();

	/** Returns a satisfying model for the current assertion set.
	 * Requires :produce-models to be enabled and the last check-sat to have returned sat;
	 * returns an error if these preconditions are not met.
	 * @return a model, unsupported, or an SMT error response
	 */
	IResponse get_model();

	/** Returns the subset of check-sat-assuming assumptions that caused the result to be unsat.
	 * Requires :produce-unsat-assumptions to be enabled; returns an error if it is not.
	 * @return a list of assumption literals, unsupported, or an SMT error response
	 */
	IResponse get_unsat_assumptions();

	/** Returns the named formulae that form an unsatisfiable core of the current assertion set.
	 * Requires :produce-unsat-cores to be enabled; returns an error if it is not.
	 * @return a list of formula names, unsupported, or an SMT error response
	 */
	IResponse get_unsat_core();

	/** Returns the values of the given expressions in the current satisfying model.
	 * Requires :produce-models to be enabled and the last check-sat to have returned sat;
	 * returns an error if these preconditions are not met.
	 * @param terms expressions to evaluate
	 * @return a list of term–value pairs, unsupported, or an SMT error response
	 */
	IResponse get_value(IExpr... terms);

	/** Returns the truth-value assignments for all named Boolean formulae in the current model.
	 * Requires :produce-assignments to be enabled and the last check-sat to have returned sat;
	 * returns an error if these preconditions are not met.
	 * @return a list of name–Boolean pairs, unsupported, or an SMT error response
	 */
	IResponse get_assignment();

	/** Returns the current value of the named option.
	 * @param option the keyword naming the option
	 * @return the option value, or unsupported, or an SMT error response
	 */
	IResponse get_option(IKeyword option);

	/** Returns the value of the named info item.
	 * @param option the info keyword
	 * @return the info value, or unsupported, or an SMT error response
	 */
	IResponse get_info(IKeyword option);
}
