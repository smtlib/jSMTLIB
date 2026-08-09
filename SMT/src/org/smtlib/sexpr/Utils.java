package org.smtlib.sexpr;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import org.smtlib.command.*;

/** Constants and reserved-word sets specific to the S-expression concrete syntax. */
public class Utils {

	/** Concrete syntax for the match token */
	public static final String MATCH      = "match";
	/** Concrete syntax for the special NUMERAL token */
	public static final String NUMERAL    = "NUMERAL";
	/** Concrete syntax for the special DECIMAL token */
	public static final String DECIMAL    = "DECIMAL";
	/** Concrete syntax for the special STRING token */
	public static final String STRING     = "STRING";
	/** Concrete syntax for the token that starts a parameterized identifier */
	public static final String UNDERSCORE = "_";
	/** Concrete syntax for the token that starts a named expression */
	public static final String NAMED_EXPR = "!";

	// SMT-LIB keyword strings used by the sexpr parser and printer; values
	// match org.smtlib.Utils but are held here so Parser/Printer need only one Utils import.
	public static final String AS      = org.smtlib.Utils.AS;
	public static final String EXISTS  = org.smtlib.Utils.EXISTS;
	public static final String FORALL  = org.smtlib.Utils.FORALL;
	public static final String LET     = org.smtlib.Utils.LET;
	public static final String LOGIC   = org.smtlib.Utils.LOGIC;
	public static final String PAR     = org.smtlib.Utils.PAR;
	public static final String THEORY  = org.smtlib.Utils.THEORY;

	/** Reserved words that are not commands (e.g. keywords, built-in tokens) */
	static public final Set<String> reservedWordsNotCommands;
	/** All reserved words (reserved-non-commands plus command names) */
	static public final Set<String> reservedWords;
	static {
		Set<String> notCmds = new HashSet<>();
		notCmds.add(NAMED_EXPR);
		notCmds.add(UNDERSCORE);
		notCmds.add(AS);
		notCmds.add(DECIMAL);
		notCmds.add(EXISTS);
		notCmds.add(FORALL);
		notCmds.add(LET);
		notCmds.add(MATCH);
		notCmds.add(NUMERAL);
		notCmds.add(PAR);
		notCmds.add(STRING);
		reservedWordsNotCommands = Collections.unmodifiableSet(notCmds);

		// When adding a new C_*.java command class, add its commandName here.
		Set<String> all = new HashSet<>(notCmds);
		all.add(C_assert.commandName);
		all.add(C_check_sat.commandName);
		all.add(C_check_sat_assuming.commandName);
		all.add(C_declare_const.commandName);
		all.add(C_declare_datatype.commandName);
		all.add(C_declare_datatypes.commandName);
		all.add(C_declare_fun.commandName);
		all.add(C_declare_sort.commandName);
		all.add(C_declare_sort_parameter.commandName);
		all.add(C_define_const.commandName);
		all.add(C_define_fun.commandName);
		all.add(C_define_fun_rec.commandName);
		all.add(C_define_funs_rec.commandName);
		all.add(C_define_sort.commandName);
		all.add(C_echo.commandName);
		all.add(C_exit.commandName);
		all.add(C_get_assertions.commandName);
		all.add(C_get_assignment.commandName);
		all.add(C_get_info.commandName);
		all.add(C_get_model.commandName);
		all.add(C_get_option.commandName);
		all.add(C_get_proof.commandName);
		all.add(C_get_unsat_assumptions.commandName);
		all.add(C_get_unsat_core.commandName);
		all.add(C_get_value.commandName);
		all.add(C_pop.commandName);
		all.add(C_push.commandName);
		all.add(C_reset.commandName);
		all.add(C_reset_assertions.commandName);
		all.add(C_set_info.commandName);
		all.add(C_set_logic.commandName);
		all.add(C_set_option.commandName);
		reservedWords = Collections.unmodifiableSet(all);
	}

	private Utils() {}
}
