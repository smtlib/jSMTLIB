package org.smtlib.test;

import org.junit.Before;
import org.junit.Test;

/** Tests for errors that are detected during type-checking rather than parsing -- i.e. the
 * input is syntactically valid, so parseExpr() alone (as exercised by ParseExpressionErrors)
 * can never produce them; TypeChecker.checkAssertion() must actually run. Both parsing and
 * type-checking are performed programmatically via TypeCheckRoot.check(). */
public class TypeChecks extends TypeCheckRoot {

	@Override
	@Before
	public void setup() {
		super.setup();
		checkResponse(solver.set_logic("AUFNIRA",null)); // Any logic that allows quantifiers
	}

	@Test
	public void forallDuplicateName() {
		check("(forall ((a Bool)(|a| Bool) ) (or a b))","Parameter list has a duplicate name: |a|");
	}

	@Test
	public void existsDuplicateName() {
		check("(exists ((a Bool)(|a| Bool) ) (or a b))","Parameter list has a duplicate name: |a|");
	}

	@Test
	public void letDuplicateName() {
		check("(let ((a 5) (|a| true) ) (ite b a 9))","Parameter list has a duplicate name: |a|");
	}

}
