/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib;

import org.smtlib.ICommand.Ideclare_fun;
import org.smtlib.ICommand.Ideclare_sort;
import org.smtlib.ICommand.Idefine_fun;
import org.smtlib.ICommand.Idefine_sort;
import org.smtlib.IExpr.IAttributeValue;
import org.smtlib.IExpr.IKeyword;


/** This class implements all the operations of the org.smtlib.ISolver interface
 *  to throw an UnsupportedOperationException
 *  Thus it can be used as a base class for a solver adapter class, if you want the 
 *  convenience of not having to implement all the operations at once.  The adapter
 *  class can simply remove AbstractSolver as a base class and retain ISolver as
 *  an interface to check that all ISolver methods are indeed present in the derived
 *  class.
 *  
 * @author David Cok
 *
 */
public abstract class AbstractSolver implements ISolver {
	
	/** @see org.smtlib.ISolver#start() */
	@Override
	public IResponse start() {
		throw new UnsupportedOperationException("AbstractSolver.start");
	}

	/** @see org.smtlib.ISolver#exit() */
	@Override
	public IResponse exit() {
		throw new UnsupportedOperationException("AbstractSolver.exit");
	}

	/** @see org.smtlib.ISolver#set_logic(String) */
	@Override
	public IResponse set_logic(String logicName, /*@Nullable*/ IPos pos) {
		throw new UnsupportedOperationException("AbstractSolver.set_logic");
	}

	/** @see org.smtlib.ISolver#push(int) */
	@Override
	public IResponse push(int number) {
		throw new UnsupportedOperationException("AbstractSolver.push");
	}

	/** @see org.smtlib.ISolver#pop(int) */
	@Override
	public IResponse pop(int number) {
		throw new UnsupportedOperationException("AbstractSolver.pop");
	}

	/** @see org.smtlib.ISolver#assertExpr(IExpr) */
	@Override
	public IResponse assertExpr(IExpr sexpr) {
		throw new UnsupportedOperationException("AbstractSolver.assertExpr");
	}

	/** @see org.smtlib.ISolver#check_sat()*/
	@Override
	public IResponse check_sat() {
		throw new UnsupportedOperationException("AbstractSolver.check_sat");
	}

	/** @see org.smtlib.ISolver#define_fun(ICommand.Idefine_fun)  */
	@Override
	public IResponse define_fun(Idefine_fun cmd) {
		throw new UnsupportedOperationException("AbstractSolver.define_fun");
	}

	/** @see org.smtlib.ISolver#declare_fun(ICommand.Ideclare_fun)  */
	@Override
	public IResponse declare_fun(Ideclare_fun cmd) {
		throw new UnsupportedOperationException("AbstractSolver.declare_fun");
	}

	/** @see org.smtlib.ISolver#define_sort(ICommand.Idefine_sort)  */
	@Override
	public IResponse define_sort(Idefine_sort cmd){
		throw new UnsupportedOperationException("AbstractSolver.define_sort");
	}

	/** @see org.smtlib.ISolver#declare_sort(ICommand.Ideclare_sort)  */
	@Override
	public IResponse declare_sort(Ideclare_sort cmd) {
		throw new UnsupportedOperationException("AbstractSolver.declare_sort");
	}

	/** @see org.smtlib.ISolver#set_option(IExpr.IKeyword,IAttributeValue)  */
	@Override
	public IResponse set_option(IKeyword option, IAttributeValue value){
		throw new UnsupportedOperationException("AbstractSolver.set_option");
	}

	/** @see org.smtlib.ISolver#set_info(IExpr.IKeyword, IAttributeValue)  */
	@Override
	public IResponse set_info(IKeyword key, IAttributeValue value){
		throw new UnsupportedOperationException("AbstractSolver.set_info");
	}

	/** @see org.smtlib.ISolver#check_sat()*/
	@Override
	public IResponse get_assertions(){
		throw new UnsupportedOperationException("AbstractSolver.get_assertions");
	}

	/** @see org.smtlib.ISolver#get_proof()*/
	@Override
	public IResponse get_proof(){
		throw new UnsupportedOperationException("AbstractSolver.get_proof");
	}

	/** @see org.smtlib.ISolver#get_unsat_core()*/
	@Override
	public IResponse get_unsat_core(){
		throw new UnsupportedOperationException("AbstractSolver.get_unsat_core");
	}

	/** @see org.smtlib.ISolver#get_value(IExpr... )*/
	@Override
	public IResponse get_value(IExpr... terms){
		throw new UnsupportedOperationException("AbstractSolver.get_value");
	}

	/** @see org.smtlib.ISolver#get_assignment()*/
	@Override
	public IResponse get_assignment(){
		throw new UnsupportedOperationException("AbstractSolver.get_assignment");
	}

	/** @see org.smtlib.ISolver#get_option(IExpr.IKeyword)*/
	@Override
	public IResponse get_option(IKeyword option){
		throw new UnsupportedOperationException("AbstractSolver.get_option");
	}

	/** @see org.smtlib.ISolver#get_info(IExpr.IKeyword)*/
	@Override
	public IResponse get_info(IKeyword option){
		throw new UnsupportedOperationException("AbstractSolver.get_info");
	}
}
