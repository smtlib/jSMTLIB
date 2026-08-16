/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.lang.reflect.Array;
import java.net.URL;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.smtlib.IExpr.IDecimal;
import org.smtlib.IExpr.IKeyword;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IParser.ParserException;
import org.smtlib.SMT.Configuration.SMTLIB;
import org.smtlib.impl.Factory;
import org.smtlib.impl.Pos;
import org.smtlib.impl.SMTExpr;
import org.smtlib.sexpr.ISexpr;
import org.smtlib.sexpr.ILexToken;
import org.smtlib.sexpr.Parser;

/** A class of static utility methods and constants for the SMT-LIB package. */
public class Utils {
	
	
	/** The name of the properties file read by jSMTLIB */
	static final public String PROPS_FILE = "jsmtlib.properties";
	
	/** The property name that specified the default solver */
	static final public String PROPS_DEFAULT_SOLVER = "org.smtlib.default-solver";
	
	/** The default prefix for the property names that identify solver executables,
	 * as in org.smtlib.solver_ZZZ */
	static final public String PROPS_SOLVER_PREFIX = "org.smtlib.solver_";
	
	/** The suffix for adapter properties, as in org.smtlib.solver_ZZZ.adapter */
	static final public String PROPS_ADAPTER_SUFFIX = ".adapter";
	
	/** The suffix for adapter properties, as in org.smtlib.solver_ZZZ.adapter */
	static final public String PROPS_EXEC_SUFFIX = ".exec";
	
	/** The suffix for adapter properties, as in org.smtlib.solver_ZZZ.adapter */
	static final public String PROPS_COMMAND_SUFFIX = ".command";
	
	/** The property giving the default logic path */
	static final public String PROPS_LOGIC_PATH = "org.smtlib.logic_path";

	/** The name of the test solver, implemented by this SMT app. */
	final static public String TEST_SOLVER = "test";

	/** The ID of the core functionality plug-in */
	final static public String PLUGIN_ID = "org.smtlib.SMT";

	/** The suffix used for SMT-LIB files */
	final static public String SUFFIX = ".smt2";

	/** Name of the Core theory */
	public static final String CORE = "Core";

	/** Name of the BitVector sort */
	public static final String BITVEC = "BitVec";

	/** The string designating an option item */
	public static final String PRINT_SUCCESS = ":print-success";  // FIXME - change remainder of Strings to IKeywords

	/** The string designating an option item */
	public static final String INTERACTIVE_MODE = ":interactive-mode";  // FIXME - name changed

	/** The string designating an option item */
	public static final String PRODUCE_ASSERTIONS = ":produce-assertions";

	/** The string designating an option item */
	public static final String GLOBAL_DECLARATIONS = ":global-declarations";

	/** The string designating an option item */
	public static final String RANDOM_SEED = ":random-seed";

	/** The string designating an option item */
	public static final String REPRODUCIBLE_RESOURCE_LIMIT = ":reproducible-resource-limit";

	/** The string designating an option item */
	public static final String VERBOSITY = ":verbosity";

	/** The string designating an option item */
	public static final String EXPAND_DEFINITIONS = ":expand-definitions";

	/** The string designating an option item */
	public static final String REGULAR_OUTPUT_CHANNEL = ":regular-output-channel";

	/** The string designating an option item */
	public static final String DIAGNOSTIC_OUTPUT_CHANNEL = ":diagnostic-output-channel";

	/** The string designating an option item */
	public static final String PRODUCE_PROOFS = ":produce-proofs";

	/** The string designating an option item */
	public static final String PRODUCE_ASSIGNMENTS = ":produce-assignments";

	/** The string designating an option item */
	public static final String PRODUCE_UNSAT_CORES = ":produce-unsat-cores";

	/** The string designating an option item */
	public static final String PRODUCE_UNSAT_ASSUMPTIONS = ":produce-unsat-assumptions";

	/** The string designating an option item */
	public static final String PRODUCE_MODELS = ":produce-models";

	/** The string designating an info item */
	public static final IKeyword ERROR_BEHAVIOR = new Factory().keyword(":error-behavior");

	/** The string designating an info item */
	public static final IKeyword NAME = new Factory().keyword(":name");

	/** The string designating an info item */
	public static final IKeyword AUTHORS = new Factory().keyword(":authors");

	/** The string designating an info item */
	public static final IKeyword VERSION = new Factory().keyword(":version");

	/** The string designating an info item */
	public static final IKeyword STATUS = new Factory().keyword(":status");

	/** The string designating an info item */
	public static final IKeyword REASON_UNKNOWN = new Factory().keyword(":reason-unknown");

	/** The string designating an info item */
	public static final IKeyword ALL_STATISTICS = new Factory().keyword(":all-statistics");

	/** The string designating an info item */
	public static final IKeyword ASSERTION_STACK_LEVELS = new Factory().keyword(":assertion-stack-levels");

	/** The response to the :authors info item */
	public static final String AUTHORS_VALUE = "David R. Cok";

	/** The response to the :name info item */
	public static final String NAME_VALUE = "SMT-LIB adapter";

	/** The response to the :version info item */
	// FIXME - must this be a string; what is the relationship to SW_VERSION?
	public static final String VERSION_VALUE = "0.0";

	/** The string designating the smtlib attribute within a logic or theory */
	public static final IKeyword SMTLIB_VERSION = new Factory().keyword(":smt-lib-version");

	/** The attribute tag for defining sorts in a theory */
	public static final IKeyword SORTS = new Factory().keyword(":sorts");

	/** The attribute tag for defining functions in a theory */
	public static final IKeyword FUNS = new Factory().keyword(":funs");

	/** The attribute tag for defining theories in a logic */
	public static final IKeyword THEORIES = new Factory().keyword(":theories");

	/** An ERROR_BEHAVIOR return value */
	public static final String CONTINUED_EXECUTION = "continued-execution";

	/** An ERROR_BEHAVIOR return value */
	public static final String IMMEDIATE_EXIT = "immediate-exit";

	/** A REASON_UNKNOWN return value */
	public static final String MEMOUT = "memout";

	/** A REASON_UNKNOWN return value */
	public static final String INCOMPLETE = "incomplete";

	/** The String for the logic symbol */
	public static final String LOGIC = "logic";

	/** The String for the theory symbol */
	public static final String THEORY = "theory";

	/** The String for the par reserved word */
	public static final String PAR = "par";

	/** The String for the as reserved word */
	public static final String AS = "as";

	/** The String for the as reserved word */
	public static final String LET = "let";

	/** The String for the as reserved word */
	public static final String FORALL = "forall";

	/** The String for the as reserved word */
	public static final String EXISTS = "exists";

	/** The String for the _ wildcard in match patterns */
	public static final String WILDCARD = "_";

	/** The String for the stdout predefined string */
	public static final String STDOUT = "stdout";

	/** The String for the stderr predefined string */
	public static final String STDERR = "stderr";

	/** String constant for boolean true. */
	static public final ISymbol TRUE = new SMTExpr.Symbol("true".intern());

	/** String constant for boolean false. */
	static public final ISymbol FALSE = new SMTExpr.Symbol("false".intern());

	// The following are canonical ISymbol constants for operator/family names that are
	// compared structurally (via ISymbol.equals(), never via .toString()) at dispatch
	// sites in TypeChecker and the logic/*.java classes. Compare the actual ISymbol
	// expression against these constants, not a String extracted from it.
	// Furthermore, these symbols may have different sorts in different contexts,
	// so don't actually use them as part of a parsed AST.

	static public final ISymbol NOT = new SMTExpr.Symbol("not".intern());
	static public final ISymbol AND = new SMTExpr.Symbol("and".intern());
	static public final ISymbol OR = new SMTExpr.Symbol("or".intern());
	static public final ISymbol IMPLIES = new SMTExpr.Symbol("=>".intern());
	static public final ISymbol EQ = new SMTExpr.Symbol("=".intern());
	static public final ISymbol DISTINCT = new SMTExpr.Symbol("distinct".intern());
	static public final ISymbol ITE = new SMTExpr.Symbol("ite".intern());

	static public final ISymbol MINUS = new SMTExpr.Symbol("-".intern());
	static public final ISymbol MULT = new SMTExpr.Symbol("*".intern());
	static public final ISymbol SLASH = new SMTExpr.Symbol("/".intern());
	static public final ISymbol DIV = new SMTExpr.Symbol("div".intern());
	static public final ISymbol MOD = new SMTExpr.Symbol("mod".intern());
	static public final ISymbol ABS = new SMTExpr.Symbol("abs".intern());
	static public final ISymbol EXP = new SMTExpr.Symbol("**".intern());

	static public final ISymbol GE = new SMTExpr.Symbol(">=".intern());
	static public final ISymbol GT = new SMTExpr.Symbol(">".intern());
	static public final ISymbol LE = new SMTExpr.Symbol("<=".intern());
	static public final ISymbol LT = new SMTExpr.Symbol("<".intern());

	static public final ISymbol STORE = new SMTExpr.Symbol("store".intern());
	static public final ISymbol SELECT = new SMTExpr.Symbol("select".intern());
	static public final ISymbol ARRAY = new SMTExpr.Symbol("Array".intern());
	static public final ISymbol ARROW = new SMTExpr.Symbol("->".intern());
	static public final ISymbol AT = new SMTExpr.Symbol("@".intern());

	static public final ISymbol BVNOT = new SMTExpr.Symbol("bvnot".intern());
	static public final ISymbol BVNEG = new SMTExpr.Symbol("bvneg".intern());
	static public final ISymbol BVAND = new SMTExpr.Symbol("bvand".intern());
	static public final ISymbol BVOR = new SMTExpr.Symbol("bvor".intern());
	static public final ISymbol BVADD = new SMTExpr.Symbol("bvadd".intern());
	static public final ISymbol BVMUL = new SMTExpr.Symbol("bvmul".intern());
	static public final ISymbol BVUDIV = new SMTExpr.Symbol("bvudiv".intern());
	static public final ISymbol BVUREM = new SMTExpr.Symbol("bvurem".intern());
	static public final ISymbol BVSHL = new SMTExpr.Symbol("bvshl".intern());
	static public final ISymbol BVLSHR = new SMTExpr.Symbol("bvlshr".intern());
	static public final ISymbol BVNAND = new SMTExpr.Symbol("bvnand".intern());
	static public final ISymbol BVNOR = new SMTExpr.Symbol("bvnor".intern());
	static public final ISymbol BVXOR = new SMTExpr.Symbol("bvxor".intern());
	static public final ISymbol BVXNOR = new SMTExpr.Symbol("bvxnor".intern());
	static public final ISymbol BVSUB = new SMTExpr.Symbol("bvsub".intern());
	static public final ISymbol BVSDIV = new SMTExpr.Symbol("bvsdiv".intern());
	static public final ISymbol BVSREM = new SMTExpr.Symbol("bvsrem".intern());
	static public final ISymbol BVSMOD = new SMTExpr.Symbol("bvsmod".intern());
	static public final ISymbol BVASHR = new SMTExpr.Symbol("bvashr".intern());
	static public final ISymbol BVCOMP = new SMTExpr.Symbol("bvcomp".intern());
	static public final ISymbol BVULT = new SMTExpr.Symbol("bvult".intern());
	static public final ISymbol BVULE = new SMTExpr.Symbol("bvule".intern());
	static public final ISymbol BVUGT = new SMTExpr.Symbol("bvugt".intern());
	static public final ISymbol BVUGE = new SMTExpr.Symbol("bvuge".intern());
	static public final ISymbol BVSLT = new SMTExpr.Symbol("bvslt".intern());
	static public final ISymbol BVSLE = new SMTExpr.Symbol("bvsle".intern());
	static public final ISymbol BVSGT = new SMTExpr.Symbol("bvsgt".intern());
	static public final ISymbol BVSGE = new SMTExpr.Symbol("bvsge".intern());
	static public final ISymbol CONCAT = new SMTExpr.Symbol("concat".intern());
	static public final ISymbol EXTRACT = new SMTExpr.Symbol("extract".intern());
	static public final ISymbol REPEAT = new SMTExpr.Symbol("repeat".intern());
	static public final ISymbol ZERO_EXTEND = new SMTExpr.Symbol("zero_extend".intern());
	static public final ISymbol SIGN_EXTEND = new SMTExpr.Symbol("sign_extend".intern());
	static public final ISymbol ROTATE_LEFT = new SMTExpr.Symbol("rotate_left".intern());
	static public final ISymbol ROTATE_RIGHT = new SMTExpr.Symbol("rotate_right".intern());
	/** Bitvector/Int conversions and overflow predicates (SMT-LIB 2.7 FixedSizeBitVectors). */
	static public final ISymbol UBV_TO_INT = new SMTExpr.Symbol("ubv_to_int".intern());
	static public final ISymbol SBV_TO_INT = new SMTExpr.Symbol("sbv_to_int".intern());
	static public final ISymbol INT_TO_BV = new SMTExpr.Symbol("int_to_bv".intern());
	static public final ISymbol BVNEGO = new SMTExpr.Symbol("bvnego".intern());
	static public final ISymbol BVUADDO = new SMTExpr.Symbol("bvuaddo".intern());
	static public final ISymbol BVSADDO = new SMTExpr.Symbol("bvsaddo".intern());
	static public final ISymbol BVUMULO = new SMTExpr.Symbol("bvumulo".intern());
	static public final ISymbol BVSMULO = new SMTExpr.Symbol("bvsmulo".intern());

	/** Canonical ISymbol form of BITVEC, for structural comparison against a parsed
	 * identifier's head symbol (see TypeChecker.isBitVec() and SymbolTable's bit-vector
	 * family check) instead of comparing via .toString(). */
	static public final ISymbol BITVEC_SYM = new SMTExpr.Symbol(BITVEC.intern());

	// The following are not static, because they depend on the version
	
	/** The set of standard options with boolean values */
	final public Set<String> boolOptions = new HashSet<String>();

	/** The set of standard options with numeric values */
	final public Set<String> numericOptions = new HashSet<String>();

	/** The set of standard options with string values */
	final public Set<String> stringOptions = new HashSet<String>();

	/** The set of default values for all standard options */
	final public Map<String, IAttributeValue> defaults = new HashMap<String, IAttributeValue>();


	static final public HashSet<IKeyword> infoKeywords = new HashSet<IKeyword>();
	static {
		for (IKeyword k : new IKeyword[] { NAME, AUTHORS, VERSION, ERROR_BEHAVIOR,
				REASON_UNKNOWN, ALL_STATISTICS, ASSERTION_STACK_LEVELS }) {
			infoKeywords.add(k);
		}

	}

	// /** The values for info characteristics as used for the test solver */
	// public final static Map<String,IAttributeValue> stringInfo = new
	// HashMap<String,IAttributeValue>();
	//
	// static {
	// // The values for standard info quantities
	// stringInfo.put(VERSION, VERSION_VALUE);
	// stringInfo.put(AUTHORS, AUTHORS_VALUE);
	// stringInfo.put(NAME, NAME_VALUE);
	// }

	/**
	 * Quotes a string, adding enclosing quotes and putting in SMT-LIBv2 escapes
	 * as needed
	 * 
	 * @param msg
	 *            String to quote
	 * @return the quoted string
	 */
	public String quote(String msg) {
		StringBuilder sb = new StringBuilder();
		sb.append('"');
		if (smtConfig.isVersion(SMTLIB.V20)) { // Version 2.0
			for (char c : msg.toCharArray()) {
				// In SMT-LIB v2.0, the only escapes within strings are for " and \
				// which are represented as \" and \\
				if (c == '"')
					sb.append("\\\"");
				else if (c == '\\')
					sb.append("\\\\");
				else
					sb.append(c);

				// Use something like the following if we ever implement C-like
				// escapes
				// Will need to add UNICODE escapes
				// if (c >= '!' && c <= '~') sb.append(c);
				// else if (c == ' ') sb.append(c);
				// else if (c == '\"') sb.append("\\\"");
				// else if (c == '\\') sb.append("\\\\");
				// else if (c == '\n') sb.append("\\n");
				// else if (c == '\t') sb.append("\\t");
				// else if (c == '\r') sb.append("\\r");
				// else if (c == '\b') sb.append("\\b");
				// else if (c == '\f') sb.append("\\f");
				// else {
				// sb.append('\\');
				// sb.append((char)('0' + ((int)c)/64));
				// sb.append((char)('0' + ((int)c)%64)/8);
				// sb.append((char)('0' + ((int)c)%8));
				// }
			}
			sb.append('"');
			return sb.toString();
		} else { // Version 2.5ff\
			for (char c : msg.toCharArray()) {
				// In SMT-LIB v2.5ff, the only escapes within strings are for "
				// which is represented as ""
				if (c == '"') sb.append('"');
			    sb.append(c);
			}
			sb.append('"');
			return sb.toString();			
		}
	}

	/**
	 * Converts a quoted string (which has enclosing double quotes) to a raw
	 * sequence of ASCII characters, undoing any SMT-LIBv2 escape sequences, and without
	 * the enclosing quotes
	 */
	public String unescape(String msg) {
		StringBuilder sb = new StringBuilder();
		int k = 1;
		int endPos = msg.length() - 1;
		if (msg.isEmpty() || msg.charAt(0) != '"') {
			smtConfig.log.logError("Malformed string literal (missing opening quote): " + msg);
			return msg;
		}
		while (k < endPos) {
			if (smtConfig.isVersion(SMTLIB.V20)) { // Version 2.0
				int kk = msg.indexOf('\\', k);
				if (kk == -1) {
					sb.append(msg.substring(k, endPos));
					break;
				} else {
					if (k < kk) sb.append(msg.substring(k, kk));
					if (kk >= endPos) {
						// backslash is the last character — no closing quote follows
						smtConfig.log.logError("Malformed string literal (backslash at end, missing closing quote): " + msg);
						break;
					}
					char c = msg.charAt(kk + 1);
					if (kk + 1 == endPos && c == '"') {
						// the escape sequence \\" consumes the closing quote — string is unterminated
						smtConfig.log.logError("Malformed string literal (closing quote consumed by escape sequence): " + msg);
						sb.append(c);
						k = kk + 2;
						break;
					}
					// In SMT-LIB v2.0, \\ is \ , \" is "
					// and \x for any other x keeps both chars (\ is not an error per spec)
					if (c == '\\' || c == '"') {
						sb.append(c);
					} else {
						sb.append('\\');
						sb.append(c);
					}
					k = kk + 2;
				}
			} else { // Version 2.5ff
				int kk = msg.indexOf('"', k);
				if (kk == -1) {
					smtConfig.log.logError("Malformed string literal (missing closing quote): " + msg);
					sb.append(msg.substring(k, endPos));
					break;
				} else if (kk == endPos) {
					sb.append(msg.substring(k, kk));
					k = endPos;
					break;
				} else {
					if (k < kk) sb.append(msg.substring(k, kk));
					char c = msg.charAt(kk + 1);
					// In SMT-LIB v2.5ff, the only escape sequence is "" (for ")
					if (c == '"') {
						sb.append(c);
					} else {
						smtConfig.log.logError("Malformed string literal (lone quote not followed by quote): " + msg);
					}
					k = kk + 2;
				}
			}
		}
		return sb.toString();
	}
	
	//////////////////// NON-STATIC MATERIAL

	/** A reference to the configuration being used for this instance of Utils. */
	protected SMT.Configuration smtConfig;

	/** Creates a Utils instance for the given configuration */
	public Utils(SMT.Configuration smtConfig) {
		this.smtConfig = smtConfig;
		{
			// Initializing all the standard smtConfig keywords
			boolOptions.add(PRINT_SUCCESS);
			boolOptions.add(EXPAND_DEFINITIONS); // Is deprecated in V2.5, but we keep it anyway
			boolOptions.add(INTERACTIVE_MODE);
			if (smtConfig.atLeastVersion(SMTLIB.V25)) boolOptions.add(PRODUCE_ASSERTIONS);
			if (smtConfig.atLeastVersion(SMTLIB.V25)) boolOptions.add(GLOBAL_DECLARATIONS);
			boolOptions.add(PRODUCE_PROOFS);
			boolOptions.add(PRODUCE_UNSAT_CORES);
			boolOptions.add(PRODUCE_UNSAT_ASSUMPTIONS);
			boolOptions.add(PRODUCE_MODELS);
			boolOptions.add(PRODUCE_ASSIGNMENTS);
			numericOptions.add(RANDOM_SEED);
			numericOptions.add(REPRODUCIBLE_RESOURCE_LIMIT);
			numericOptions.add(VERBOSITY);
			stringOptions.add(REGULAR_OUTPUT_CHANNEL);
			stringOptions.add(DIAGNOSTIC_OUTPUT_CHANNEL);
			defaults.put(PRINT_SUCCESS, TRUE);
			defaults.put(EXPAND_DEFINITIONS, FALSE); 
			defaults.put(INTERACTIVE_MODE, FALSE);
			if (smtConfig.atLeastVersion(SMTLIB.V25)) defaults.put(PRODUCE_ASSERTIONS, FALSE);
			if (smtConfig.atLeastVersion(SMTLIB.V25)) defaults.put(GLOBAL_DECLARATIONS, FALSE);
			defaults.put(PRODUCE_PROOFS, FALSE);
			defaults.put(PRODUCE_UNSAT_CORES, FALSE);
			defaults.put(PRODUCE_UNSAT_ASSUMPTIONS, FALSE);
			defaults.put(PRODUCE_MODELS, FALSE);
			defaults.put(PRODUCE_ASSIGNMENTS, FALSE);
			defaults.put(RANDOM_SEED, new SMTExpr.Numeral(0));
			defaults.put(REPRODUCIBLE_RESOURCE_LIMIT, new SMTExpr.Numeral(0));
			defaults.put(VERBOSITY, new SMTExpr.Numeral(0));
			defaults.put(REGULAR_OUTPUT_CHANNEL, new SMTExpr.StringLiteral(STDOUT,
					false));
			defaults.put(DIAGNOSTIC_OUTPUT_CHANNEL, new SMTExpr.StringLiteral(
					STDERR, false));
		}
	}

	/**
	 * Opens an InputStream for a named logic or theory file.
	 * Searches the configured logicPath directories first, then falls back to the
	 * system classpath (with a versioned subfolder prefix when no path is set and
	 * an older SMT-LIB version is configured).
	 *
	 * @param name the logic or theory name (filename without .smt2 suffix)
	 * @param pos  source position for error messages, or null
	 * @throws SMTLIBException if the file cannot be found or opened
	 */
	private InputStream openLogicStream(String name, IPos pos) throws SMTLIBException {
		String filename = name + SUFFIX;
		String path = smtConfig.logicPath;
		try {
			if (path != null) {
				// Explicit path: each component must be a real directory -- a mistyped
				// component is a configuration error and should fail loudly rather than be
				// silently treated as "not found here, try the next component". Components
				// use the same separator character as the Java classpath (File.pathSeparator).
				for (String d : path.split(File.pathSeparator)) {
					if (!new File(d).isDirectory()) {
						throw new SMTLIBException(smtConfig.responseFactory.error(
								"Invalid logic path: \"" + d + "\" is not a directory", pos));
					}
				}
				for (String d : path.split(File.pathSeparator)) {
					File f = new File(d + File.separator + filename);
					if (f.exists()) return new FileInputStream(f);
				}
				// Not overridden on this (valid) path: an explicit logic path may deliberately
				// supply only some logics/theories and rely on the built-in definitions for
				// everything else, so always fall through to the classpath below.
			}
			// No explicit path, or not found on a valid explicit path: try the versioned
			// subfolder in the classpath first (built-in definitions are organized by
			// SMT-LIB version), then the top-level (latest-version) copy.
			List<String> candidates = new ArrayList<>();
			if (smtConfig.smtlib != null) {
				SMTLIB cv = SMTLIB.find(smtConfig.smtlib);
				SMTLIB latest = SMTLIB.values()[SMTLIB.values().length - 1];
				if (cv != null && cv != latest) candidates.add(cv.id + "/" + filename);
			}
			candidates.add(filename);
			for (String candidate : candidates) {
				URL url = ClassLoader.getSystemResource(candidate);
				if (url != null) return url.openStream();
			}
			throw new SMTLIBException(smtConfig.responseFactory.error(
					path == null ? "No logic file found for " + name
							: "No logic file found for " + name + " on path \"" + path + "\"",
					pos));
		} catch (IOException e) {
			throw new SMTLIBException(smtConfig.responseFactory.error(
					"Failed to open logic file for " + name + ": " + e, pos));
		}
	}

	/**
	 * Reads a logic file, parses it, validates the name, and checks the version.
	 *
	 * @param name the logic name (and base filename)
	 * @param pos  source position for error messages, or null
	 * @return the parsed ILogic
	 * @throws SMTLIBException if the file cannot be found, parsed, or validated
	 */
	public ILogic findLogic(String name, IPos pos) throws SMTLIBException {
		InputStream input = null;
		try {
			input = openLogicStream(name, pos);
			SMT.Configuration config = smtConfig.clone();
			config.interactive = false;
			ISource source = config.smtFactory.createSource(config, input, null);
			IParser p = config.smtFactory.createParser(config, source);
			ILogic logic = p.parseLogic();
			if (!name.equals(logic.logicName().value())) {
				throw new SMTLIBException(smtConfig.responseFactory.error(
						"Logic file for " + name + " declares logic name '"
						+ logic.logicName().value() + "'"));
			}
			IResponse.IError verErr = checkVersion("Logic", name, logic.value(SMTLIB_VERSION));
			if (verErr != null) throw new SMTLIBException(verErr);
			return logic;
		} catch (IParser.ParserException e) {
			throw new SMTLIBException(smtConfig.responseFactory.error(
					"Failed to parse the logic file for " + name + ": " + e, e.pos()));
		} catch (SMTLIBException e) {
			throw e;
		} catch (Exception e) {
			throw new SMTLIBException(smtConfig.responseFactory.error(
					"Failed to read the logic file for " + name + ": " + e, null));
		} finally {
			try { if (input != null) input.close(); }
			catch (IOException e) {
				throw new SMTLIBException(smtConfig.responseFactory.error(
						"Failed to close a stream while parsing " + name + ": " + e, null));
			}
		}
	}

	/**
	 * Checks that a :smt-lib-version attribute value is a recognised decimal version
	 * and that the configured version is at least as new. Returns an error response if
	 * any check fails; returns null if the attribute is absent or all checks pass.
	 *
	 * @param kind  "Logic" or "Theory" (used in error messages)
	 * @param name  the logic/theory name (used in error messages)
	 * @param ver   the raw attribute value from the parsed file (may be null if absent)
	 */
	private IResponse.IError checkVersion(String kind, String name, IAttributeValue ver) {
		if (ver == null) return null;
		if (!(ver instanceof IExpr.IDecimal)) {
			return smtConfig.responseFactory.error(
					kind + " " + name + ": the value of " + SMTLIB_VERSION
					+ " is not a decimal number: " + ver);
		}
		SMTLIB tv = SMTLIB.find("V" + ver.toString());
		if (tv == null) {
			return smtConfig.responseFactory.error(
					kind + " " + name + ": unrecognized SMT-LIB version: " + ver);
		}
		if (!smtConfig.atLeastVersion(tv) && !smtConfig.relax) {
			return smtConfig.responseFactory.error(
					kind + " " + name + " requires SMT-LIB " + ver
					+ " but the configured version is older");
		}
		return null;
	}

	/**
	 * Reads a theory file, returning the S-expression that it holds.
	 * 
	 * @param name
	 *            the name of the theory
	 * @param path
	 *            the directory path in which theory files are stored
	 * @return an ISexpr that holds a theory definition
	 * @throws SMTLIBException if an error occurs
	 */
	// FIXME Fix the use of path here - it actually is used only for error messages and should not be null
	public ITheory findTheory(String name, /* @Nullable */ String path) throws SMTLIBException {
		ISource source;
		InputStream input = null;
		try {
			SMT.Configuration config = smtConfig.clone();
			config.interactive = false;
			input = openLogicStream(name, null);
			source = config.smtFactory.createSource(config, input, null);
			IParser p = config.smtFactory.createParser(config, source);
			ITheory th = p.parseTheory();
			if (!name.equals(th.theoryName().value())) {
				throw new SMTLIBException(smtConfig.responseFactory.error(
						"Theory file for " + name + " declares theory name '"
						+ th.theoryName().value() + "'"));
			}
			IResponse.IError verErr = checkVersion("Theory", name, th.value(SMTLIB_VERSION));
			if (verErr != null) throw new SMTLIBException(verErr);
			return th;
		} catch (IParser.ParserException e) {
			throw new SMTLIBException(smtConfig.log.logError(smtConfig.responseFactory.error(
					"Failed to parse the theory file " + name + " in " + path
							+ ": " + e, e.pos())));
		} catch (SMTLIBException e) {
			throw e;
		} catch (Exception e) {
			throw new SMTLIBException(smtConfig.log.logError(smtConfig.responseFactory.error(
					"Failed to read the theory file " + name + " in " + path
							+ ": " + e, null)));
		} finally {
			try {
				if (input != null) input.close();
			} catch (java.io.IOException e) {
				throw new SMTLIBException(smtConfig.log.logError(smtConfig.responseFactory.error(
						"Failed to close a stream while parsing " + name
								+ " in " + path + " : " + e, null)));
			}
		}
	}

	/**
	 * Finds and loads a logic into the given symbol table
	 * 
	 * @param logicName
	 *            name of the logic to load
	 * @param symTable
	 *            the symbol table into which to load it
	 * @return null if read OK, an error if a problem happened
	 */
	public/* @Nullable */IResponse loadLogic(String logicName,
			SymbolTable symTable, /* @Nullable */IPos pos) {
		ILogic sx;
		try {
			sx = findLogic(logicName, pos);
		} catch (SMTLIBException e) {
			return e.errorResponse;
		}
		symTable.logicInUse = sx;
		return loadLogic(sx, symTable);
	}

	/**
	 * Loads a theory into the given symbol table.
	 * 
	 * @param theoryName
	 *            the theory to load
	 * @param symTable
	 *            the symbol table into which to put the theory
	 * @return null if OK, otherwise an error as a IResponse
	 */
	public/* @Nullable */IResponse loadTheory(String theoryName,
			SymbolTable symTable) {
		ITheory th = null;
		try {
			th = findTheory(theoryName, smtConfig.logicPath);
		} catch (SMTLIBException e) {
			return e.errorResponse;
		}

		if (smtConfig.verbose != 0) {
			smtConfig.log.logDiag("#Installing theory " + theoryName);
		}
		
		/* @Nullable */IResponse response = loadTheory(th, symTable);
		if (response == null) {
			if (theoryName.equals("ArraysEx"))
				symTable.arrayTheorySet = true;
			if (theoryName.equals("Fixed_Size_BitVectors") || theoryName.equals("FixedSizeBitVectors"))
				symTable.bitVectorTheorySet = true;
			if (theoryName.equals("Reals_Ints"))
				symTable.realsIntsTheorySet = true;
			if (theoryName.equals("HO-Core"))
				symTable.hoTheorySet = true;
		}
		return response;
	}

	private <T extends IPos.IPosable> T setPos(T p, IPos pos) { p.setPos(pos); return p; }

	public /* @Nullable */ IResponse loadLogic(ILogic logicExpr, SymbolTable symTable) {
		String logicName = logicExpr.logicName().value();

		IAttributeValue version = logicExpr.value(SMTLIB_VERSION);
		if (version == null) return smtConfig.responseFactory.error("Logic definition for " + logicName + " is missing the " + SMTLIB_VERSION + " attribute");

		IAttributeValue o = logicExpr.value(THEORIES);
		if (!(o instanceof ISexpr.ISeq)) {
			return smtConfig.responseFactory.error("Expected a list of theories for the value of the " + THEORIES + " attribute");
		}
		IResponse res = loadTheory(CORE, symTable);
		if (res != null) return res;
		ISexpr.ISeq theories = (ISexpr.ISeq) o;
		for (ISexpr theory : theories.sexprs()) {
			if (!(theory instanceof IExpr.ISymbol)) return smtConfig.responseFactory.error("Expected a simple symbol to designate a theory");
			ISymbol theoryName = (IExpr.ISymbol) theory;
			if (CORE.equals(theoryName.value())) continue;
			if ("ALL".equals(logicName)) {
				boolean savedRelax = smtConfig.relax;
				String savedSmtlib = smtConfig.smtlib;
				smtConfig.relax = true;
				smtConfig.smtlib = null;
				ITheory th;
				try {
					th = findTheory(theoryName.value(), smtConfig.logicPath);
				} catch (SMTLIBException e) {
					return e.errorResponse;
				} finally {
					smtConfig.relax = savedRelax;
					smtConfig.smtlib = savedSmtlib;
				}
				IAttributeValue tv = th.value(SMTLIB_VERSION);
				if (tv instanceof IDecimal) {
					SMT.Configuration.SMTLIB ver = SMT.Configuration.SMTLIB.find("V" + tv.toString());
					if (ver != null && !smtConfig.atLeastVersion(ver)) continue;
				}
				res = loadTheory(th, symTable);
				if (res == null) {
					String tname = th.theoryName().value();
					if (tname.equals("ArraysEx")) symTable.arrayTheorySet = true;
					if (tname.equals("Fixed_Size_BitVectors") || tname.equals("FixedSizeBitVectors")) symTable.bitVectorTheorySet = true;
					if (tname.equals("Reals_Ints")) symTable.realsIntsTheorySet = true;
					if (tname.equals("HO-Core")) symTable.hoTheorySet = true;
				}
			} else {
				res = loadTheory(theoryName.value(), symTable);
			}
			if (res != null) return res;
		}
		return null;
	}

	public /* @Nullable */ IResponse loadTheory(ITheory theory, SymbolTable symTable) {
		String theoryName = theory.theoryName().value();

		IAttributeValue version = theory.value(SMTLIB_VERSION);
		if (version == null) return smtConfig.responseFactory.error("Theory definition for " + theoryName + " is missing the " + SMTLIB_VERSION + " attribute");

		for (IAttributeValue sortsVal : theory.values(SORTS)) {
			if (!(sortsVal instanceof ISexpr.ISeq)) {
				return smtConfig.responseFactory.error("The list of sorts in theory " + theoryName + " is ill-formed: " + sortsVal);
			}
			Iterator<ISexpr> iter = ((ISexpr.ISeq) sortsVal).sexprs().iterator();
			while (iter.hasNext()) {
				ISexpr.ISeq sx = (ISexpr.ISeq) iter.next();
				Iterator<ISexpr> iter2 = sx.sexprs().iterator();
				IExpr.ISymbol name = (IExpr.ISymbol) iter2.next();
				INumeral arity = (IExpr.INumeral) iter2.next();
				ISexpr key = iter2.hasNext() ? iter2.next() : null;
				if (key != null && !(key instanceof IExpr.IKeyword)) {
					return smtConfig.responseFactory.error("Ill-formed attribute in the declaration of sort " + name + ": " + key);
				}
				List<IExpr.IAttribute<?>> attrs = parseAttributeTail(iter2, key);
				symTable.addSortDefinition(name, arity, attrs, true);
				if (smtConfig.verbose != 0) smtConfig.log.logDiag("#Added sort " + name);
			}
		}

		for (IAttributeValue funsVal : theory.values(FUNS)) {
			IResponse r = loadFuns(funsVal, theoryName, symTable);
			if (r != null) return r;
		}
		if (theoryName.equals("ArraysEx")) {
			ISort.IFcnSort fs = smtConfig.sortFactory.createFcnSort(new ISort[0], null);
			SymbolTable.Entry e = new SymbolTable.Entry(smtConfig.exprFactory.symbol("store"), fs, null, null);
			symTable.add(e, true);
			e = new SymbolTable.Entry(smtConfig.exprFactory.symbol("select"), fs, null, null);
			symTable.add(e, true);
		}
		if (theoryName.equals("HO-Core")) {
			// @ is declared in HO-Core.smt2 as (par (A B) (@ (-> A B :left-assoc) A B)) --
			// loadFuns() skips any :funs entry beginning with "par" (no par-polymorphic
			// function support exists), so @ is never registered by the loop above. As with
			// store/select, register a placeholder entry (empty/null sort: not used for
			// type-checking, which for @ is still done by TypeChecker.visit(IFcnExpr)'s own
			// hoTheorySet-gated special case) just so the name is marked defined.
			ISort.IFcnSort fs = smtConfig.sortFactory.createFcnSort(new ISort[0], null);
			SymbolTable.Entry e = new SymbolTable.Entry(smtConfig.exprFactory.symbol("@"), fs, null, null);
			symTable.add(e, true);
		}

		return null;
	}

	/** Parses a trailing attribute* tail (keyword [value] pairs) from a sort_symbol_decl or
	 * fun_symbol_decl's sexpr, given the first attribute keyword already read from the
	 * iterator (or null if there is no attribute tail at all). Shared by loadTheory's sort
	 * declarations and loadFuns' function declarations, since both end with the same
	 * attribute* grammar production. */
	private List<IExpr.IAttribute<?>> parseAttributeTail(Iterator<ISexpr> iter2, /*@Nullable*/ ISexpr firstKey) {
		List<IExpr.IAttribute<?>> attrs = new LinkedList<IExpr.IAttribute<?>>();
		ISexpr key = firstKey;
		if (key != null) while (true) {
			if (iter2.hasNext()) {
				ISexpr key2 = iter2.next();
				if (key2 instanceof IExpr.IKeyword) {
					attrs.add(setPos(smtConfig.exprFactory.attribute((IExpr.IKeyword) key, null), key.pos()));
					key = key2;
				} else {
					attrs.add(setPos(smtConfig.exprFactory.attribute((IExpr.IKeyword) key, key2),
							new Pos(key.pos().charStart(), key2.pos().charEnd(), key.pos().source())));
					if (!iter2.hasNext()) break;
					// keyword-with-value followed by more attributes (e.g. ":weight 3 :chainable");
					// no current theory exercises this path but it is correct and must remain.
					key = iter2.next();
				}
			} else {
				attrs.add(setPos(smtConfig.exprFactory.attribute((IExpr.IKeyword) key, null), key.pos()));
				break;
			}
		}
		return attrs;
	}

	private /* @Nullable */ IResponse loadFuns(IAttributeValue funsVal, String theoryName, SymbolTable symTable) {
		if (!(funsVal instanceof ISexpr.ISeq)) return smtConfig.responseFactory.error("Expected a sequence of function declarations instead of " + funsVal);
		Iterator<ISexpr> iter = ((ISexpr.ISeq) funsVal).sexprs().iterator();
		while (iter.hasNext()) {
			ISexpr next = iter.next();
			if (!(next instanceof ISexpr.ISeq)) continue;
			ISexpr.ISeq sx = (ISexpr.ISeq) next;
			ISexpr first = sx.sexprs().get(0);
			if (!(first instanceof IExpr.ISymbol)) continue;
			IExpr.ISymbol sym = (IExpr.ISymbol) first;
			String name = sym.value();
			if (name.equals(PAR)) {
				IResponse r = loadParFun(sx, theoryName, symTable);
				if (r != null) return r;
				continue;
			}
			Iterator<ISexpr> iter2 = sx.sexprs().iterator();
			iter2.next();
			List<ISort> sorts = new LinkedList<ISort>();
			ISexpr key = null;
			while (iter2.hasNext()) {
				key = iter2.next();
				if (key instanceof IExpr.IKeyword) break;
				ISort ss = asSort(key, symTable);
				if (ss == null) return smtConfig.responseFactory.error("Unknown sort given: " + key);
				sorts.add(ss);
				key = null;
			}
			ISort result = sorts.remove(sorts.size() - 1);
			List<IExpr.IAttribute<?>> attrs = parseAttributeTail(iter2, key);
			ISort.IFcnSort fcnSort = smtConfig.sortFactory.createFcnSort(sorts.toArray(new ISort[sorts.size()]), result);
			boolean b = symTable.add(new SymbolTable.Entry(sym, fcnSort, attrs, null), true, true);
			if (!b) return smtConfig.responseFactory.error("Failed to add to symbol table: " + smtConfig.defaultPrinter.toString(sym) + " " + smtConfig.defaultPrinter.toString(fcnSort));
			if (smtConfig.verbose != 0) smtConfig.log.logDiag("#Added symbol " + name);
		}
		return null;
	}

	/** Parses a par_fun_symbol_decl, ( par ( symbol+ ) ( identifier sort+ attribute* ) ),
	 * registering a poly Entry whose sort/attributes may reference the declared parameters
	 * as ISort.IParameter placeholders (e.g. HO-Core.smt2's (par (A B) (@ (-> A B) A B
	 * :left-assoc))). The parameter symbols are bound as arity-0 sorts in a scope pushed
	 * just for resolving this one declaration -- the same technique
	 * TypeChecker.checkSortAbbreviation() uses for a define-sort's own parameters -- so that
	 * asSort() can resolve occurrences of them the same way it resolves any other sort name. */
	private /* @Nullable */ IResponse loadParFun(ISexpr.ISeq parDecl, String theoryName, SymbolTable symTable) {
		List<ISexpr> parElems = parDecl.sexprs();
		if (parElems.size() != 3 || !(parElems.get(1) instanceof ISexpr.ISeq) || !(parElems.get(2) instanceof ISexpr.ISeq)) {
			return smtConfig.responseFactory.error("Ill-formed par function declaration in theory " + theoryName + ": " + parDecl);
		}
		List<ISexpr> paramSyms = ((ISexpr.ISeq) parElems.get(1)).sexprs();
		ISexpr.ISeq decl = (ISexpr.ISeq) parElems.get(2);
		if (decl.sexprs().isEmpty() || !(decl.sexprs().get(0) instanceof IExpr.ISymbol)) {
			return smtConfig.responseFactory.error("Ill-formed par function declaration in theory " + theoryName + ": " + parDecl);
		}
		IExpr.ISymbol sym = (IExpr.ISymbol) decl.sexprs().get(0);

		symTable.push();
		try {
			List<ISort.IParameter> params = new LinkedList<ISort.IParameter>();
			for (ISexpr pe : paramSyms) {
				if (!(pe instanceof IExpr.ISymbol)) {
					return smtConfig.responseFactory.error("Ill-formed parameter in theory " + theoryName + ": " + pe);
				}
				IExpr.ISymbol psym = (IExpr.ISymbol) pe;
				if (!symTable.addSortParameter(psym, false)) {
					return smtConfig.responseFactory.error("Duplicate parameter " + psym + " in theory " + theoryName);
				}
				params.add((ISort.IParameter) symTable.lookupSort(psym));
			}

			Iterator<ISexpr> iter2 = decl.sexprs().iterator();
			iter2.next();
			List<ISort> sorts = new LinkedList<ISort>();
			ISexpr key = null;
			while (iter2.hasNext()) {
				key = iter2.next();
				if (key instanceof IExpr.IKeyword) break;
				ISort ss = asSort(key, symTable);
				if (ss == null) return smtConfig.responseFactory.error("Unknown sort given: " + key);
				sorts.add(ss);
				key = null;
			}
			ISort result = sorts.remove(sorts.size() - 1);
			List<IExpr.IAttribute<?>> attrs = parseAttributeTail(iter2, key);
			ISort.IFcnSort fcnSort = smtConfig.sortFactory.createFcnSort(sorts.toArray(new ISort[sorts.size()]), result);
			boolean b = symTable.add(new SymbolTable.Entry(sym, fcnSort, attrs, params), true, true);
			if (!b) return smtConfig.responseFactory.error("Failed to add to symbol table: " + smtConfig.defaultPrinter.toString(sym));
			if (smtConfig.verbose != 0) smtConfig.log.logDiag("#Added symbol " + sym.value());
		} finally {
			symTable.pop();
		}
		return null;
	}

	public /* @Nullable */ ISort asSort(ISexpr sexpr, SymbolTable symtab) {
		if (sexpr instanceof IExpr.ISymbol) {
			IExpr.ISymbol sym = (IExpr.ISymbol) sexpr;
			ISort.IDefinition def = symtab.lookupSort(sym);
			if (def == null || def.intArity() != 0) return null;
			// A par-declared parameter (e.g. A, B in (par (A B) ...)) must be returned as-is,
			// not wrapped in a fresh sort application: IParameter.equals() is identity-based,
			// so later substitution/unification needs this to be the very same object that
			// was bound for this parameter, not a new node that merely refers to it.
			if (def instanceof ISort.IParameter) return (ISort.IParameter) def;
			ISort.IApplication sort = smtConfig.sortFactory.createSortExpression(def.identifier());
			sort.definition(def);
			return sort;
		}
		if (sexpr instanceof ISexpr.ISeq) {
			// A compound sort expression, e.g. (-> A B): the head must be a declared sort
			// family (not an abbreviation or parameter -- those aren't callable like this),
			// and each remaining element is itself resolved recursively (so this also handles
			// nested compound sorts and parameter references anywhere within).
			List<ISexpr> elems = ((ISexpr.ISeq) sexpr).sexprs();
			if (elems.isEmpty() || !(elems.get(0) instanceof IExpr.ISymbol)) return null;
			ISort.IDefinition def = symtab.lookupSort((IExpr.ISymbol) elems.get(0));
			if (!(def instanceof ISort.IFamily)) return null;
			List<ISort> args = new LinkedList<ISort>();
			for (int i = 1; i < elems.size(); i++) {
				ISort arg = asSort(elems.get(i), symtab);
				if (arg == null) return null;
				args.add(arg);
			}
			if (args.size() != def.intArity()) return null;
			return def.eval(args);
		}
		return null;
	}

	/** A checked exception used internally to propagate SMT-LIB errors that carry an IResponse.IError. */
	static public class SMTLIBException extends Exception {
		private static final long serialVersionUID = 1L;
		/** The error response describing the problem that caused this exception. */
		@SuppressWarnings("serial")
		public IResponse.IError errorResponse;

		/** Creates an SMTLIBException wrapping the given error response. */
		public SMTLIBException(IResponse.IError err) {
			this.errorResponse = err;
		}
	}
	
    /** Concatenates two or more arrays of the same component type into a single new array. */
    @SafeVarargs // requires an argument that is not empty
    public static <T> T[] cat(T[] ... arrays) {
        int n = 0;
        for (T[] a: arrays) n += a.length;
        @SuppressWarnings("unchecked")
        T[] r = (T[])Array.newInstance(arrays[0].getClass(), n);
        int k = 0;
        for (T[] a: arrays) {
            System.arraycopy(a,  0,  r,  k, a.length);
            k += a.length;
        }
        return r;
    }

    /** Concatenates an array and additional individual elements into a single new array. */
    @SafeVarargs
    @SuppressWarnings("varargs")
    public static <T> T[] cat(T[] aa, T ... rest) {
        int n = aa.length + rest.length;
        @SuppressWarnings("unchecked")
        T[] r = (T[])Array.newInstance(aa[0].getClass(), n);
        System.arraycopy(aa,  0,  r,  0, aa.length);
        System.arraycopy(rest,  0,  r,  aa.length, rest.length);
        return r;
    }
    
    /** Called at branches that should never be executed in a correct program;
     *  prints a stack trace so that JaCoCo coverage failures are immediately visible. */
    public static void jacocoNeverExecuted() {
        RuntimeException e = new RuntimeException("Utils.jacocoNeverExecuted is unexpectedly called");
        System.out.println(e.getMessage());
        e.printStackTrace(System.out);
    }

}
