/**
 * This class is part of the SMT Plugin
 * @author David R. Cok
 * September 2010
 */
package org.smtlib.plugin.editor;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.rules.*;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.widgets.Display;

/** This class defines tokens and the syntax rules that go along with those tokens, and sets the
 * associated syntax coloring.
 * 
 * If you are going to add a new token type you need to do the following:
 * <UL>
 * <LI> Add a String constant in SMTPartitionScanner (e.g. SMT_SYMBOL)
 * <LI> Add the string to SMTPartitionScanner.tokenNames
 * <LI> Define a new IToken in SMTPartitionScanner (e.g. smtSymbol)
 * <LI> Associate the token with a rule in SMTPartitionScanner()
 * <LI> Define a color for the token in ISMTColorConstants (e.g. ISMTColorConstants.SMT_SYMBOL)
 * <LI> In SMTConfiguration.getPresentationReconciler(ISourceViewer sourceViewer) follow the 
 *      pattern to add code that associates the desired color with the symbol
 * </UL>
 * @author David R. Cok
 */
// TODO - fix the documentation above
public class SMTPartitionScanner extends RuleBasedScanner implements IPartitionTokenScanner {
	/* Define unique strings that identify each token */
	public final static String SMT_DEFAULT = "__smt_default";
	public final static String SMT_COMMENT = "__smt_comment";
	public final static String SMT_PAREN = "__smt_paren";
	public final static String SMT_NUMERAL = "__smt_numeral";
	public final static String SMT_KEYWORD = "__smt_keyword";
	public final static String SMT_SYMBOL = "__smt_symbol";
	public final static String SMT_QSYMBOL = "__smt_qsymbol";
	public final static String SMT_DECIMAL = "__smt_decimal";
	public final static String SMT_HEX = "__smt_hex";
	public final static String SMT_BINARY = "__smt_binary";
	public final static String SMT_COMMAND = "__smt_command";
	public final static String SMT_STRING = "__smt_string";
	public final static String SMT_RESERVED_WORD = "__smt_reserved_word";
	public final static String SMT_INVALID = "__smt_invalid";
	
	public final static String[] tokenNamesWithDefault = new String[]{ 
		SMT_COMMENT, SMT_NUMERAL, SMT_SYMBOL, SMT_KEYWORD, SMT_STRING, SMT_QSYMBOL, SMT_PAREN,
		SMT_DECIMAL, 
		SMT_HEX, SMT_BINARY, SMT_COMMAND, SMT_RESERVED_WORD, SMT_INVALID,
		IDocument.DEFAULT_CONTENT_TYPE,
	};

	public final static String[] tokenNames = new String[]{ 
		SMT_COMMENT, SMT_PAREN, SMT_NUMERAL, SMT_DECIMAL, SMT_SYMBOL, SMT_KEYWORD, 
		SMT_QSYMBOL, SMT_HEX, SMT_BINARY, SMT_COMMAND, SMT_STRING, SMT_RESERVED_WORD, SMT_INVALID
	};
	
	public final static Token token(RGB rgb) {
		return new Token(new TextAttribute(new Color(Display.getCurrent(),rgb)));
	}

	/* Create a token, each one associated with a token that contains the text attribute we want for that token. */
	public final static IToken smtDefault = token(ISMTColorConstants.DEFAULT);
	public final static IToken smtComment = token(ISMTColorConstants.SMT_COMMENT);
	public final static IToken smtParen = token(ISMTColorConstants.SMT_PAREN);
	public final static IToken smtBinary = token(ISMTColorConstants.SMT_BINARY);
	public final static IToken smtHex = token(ISMTColorConstants.SMT_HEX);
	public final static IToken smtNumeral = token(ISMTColorConstants.SMT_NUMERAL);
	public final static IToken smtKeyword = token(ISMTColorConstants.SMT_KEYWORD);
	public final static IToken smtSymbol = token(ISMTColorConstants.SMT_SYMBOL);
	public final static IToken smtQSymbol = token(ISMTColorConstants.SMT_QSYMBOL);
	public final static IToken smtDecimal = token(ISMTColorConstants.SMT_DECIMAL);
	public final static IToken smtString = token(ISMTColorConstants.SMT_STRING);
	public final static IToken smtCommand = token(ISMTColorConstants.SMT_COMMAND);
	public final static IToken smtReservedWord = token(ISMTColorConstants.SMT_RESERVED_WORD);
	public final static IToken smtInvalid = token(ISMTColorConstants.SMT_INVALID);


	final static public String[] _reservedWords = {
		"_", "!", "as", "NUMERAL", "DECIMAL", "STRING", "forall", "exists", "let", "par",
		"assert", "check-sat", 
		"declare-fun", "define-fun", "declare-sort", "define-sort",
		"exit", "get-info", "get-option", 
		"get-proof", "get-assignment", "get-assertions", "get-unsat-core", "get-value",
		"push", "pop",
		"set-logic", "set-info", "set-option"};

	final static public Set<String> reservedWords = new HashSet<String>();
	static {
		for (String s: _reservedWords) reservedWords.add(s);
	}
	
	public SMTPartitionScanner() {
		/* Associate a rule with each token */
		/*@Mutable*/
		IRule[] rules = new IRule[] {
				new EndOfLineRule(";", smtComment),
				new WhitespaceRule(new IWhitespaceDetector() { public boolean isWhitespace(char c) { return c == ' ' || c == '\t' || c == '\n' || c == '\r'; }}),
				new NumberDecimalRule(smtNumeral,smtDecimal,smtInvalid), 
//				new NumberRule(smtNumeral),
				new WordRule(new CharDetector("()"), smtParen),
				
				new WordRule(new KeywordDetector(), smtKeyword),
//				new WordRule(new SymbolDetector(), smtSymbol),
				new SymbolRWRule(smtSymbol,smtReservedWord,reservedWords),
//				//new WordRule(new StringDetector(), smtString),
				new PatternRule("\"","\"", smtString, '\\',false),
				new PatternRule("\"","\"", smtInvalid, '\\', false, true), // unclosed string
				new PatternRule("|","|", smtQSymbol, (char)-1, false),
				new PatternRule("|","|", smtInvalid, (char)-1, false, true), // unclosed symbol
				
				// FIXME - bad characters in |-symbol, in string

				new BinHexRule(smtBinary,smtHex,smtInvalid), 
				new WordRule(new PrintableDetector(), smtInvalid),
		};

		setRules(rules);
	}
	
	@Override
	public void setPartialRange(IDocument arg0, int arg1, int arg2,
			String arg3, int arg4) {
		// TODO Auto-generated method stub ????? Don't know what this is supposed to do
	}
	
	// FIXME - some performance improvement could be done here

	/* Define a bunch of useful character classes */
	public final static String whitespace = " \t\r\n";
	public final static String digits = "0123456789";
	public final static String alpha = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";
	public final static String sympunc = "_-+~!@$%^&*=<>.?/";
	public final static String allpunc = "_-+~!@$%^&*=<>.?/';:|{}[]()`,#\"\\";
	public final static String nondigitsymchar = alpha + sympunc;
	public final static String symchar = digits + alpha + sympunc;
	public final static String printable = whitespace + digits + alpha + allpunc;
	
	/** Defines a IRule detector for an SMTLIB keyword */
	static private class KeywordDetector implements IWordDetector {

		@Override
		public boolean isWordPart(char c) {
			return symchar.indexOf(c) >= 0;
		}

		@Override
		public boolean isWordStart(char c) {
			return c == ':';
		}
		
	}

//	/** Defines a IRule detector for an SMTLIB non-quoted symbol */
//	static private class SymbolDetector implements IWordDetector {
//
//		@Override
//		public boolean isWordPart(char c) {
//			return symchar.indexOf(c) >= 0;
//		}
//
//		@Override
//		public boolean isWordStart(char c) {
//			return nondigitsymchar.indexOf(c) >= 0;
//		}
//	}

	/** Defines a IRule detector for a sequence of given characters. */
	static private class CharDetector implements IWordDetector {
		String ch;
		public CharDetector(String ch) {
			this.ch = ch;
		}
		@Override
		public boolean isWordPart(char c) {
			return ch.indexOf(c) >= 0;
		}

		@Override
		public boolean isWordStart(char c) {
			return isWordPart(c);
		}
	}

	/** Defines a IRule detector for a sequence of printable characters */
	static private class PrintableDetector implements IWordDetector {
		public PrintableDetector() {
		}
		
		@Override
		public boolean isWordPart(char c) {
			//return c >= '!' && c <= '~';
			return ",;'{}[]`".indexOf(c) >= 0;
		}

		@Override
		public boolean isWordStart(char c) {
			return isWordPart(c);
		}
	}

//	/** Defines a IRule detector for an SMTLIB string literal */
//	static private class StringDetector implements IWordDetector {
//
//		@Override
//		public boolean isWordPart(char c) {
//			return c != '"';
//		}
//
//		@Override
//		public boolean isWordStart(char c) {
//			return c == '"';
//		}
//	}

	/** This detector identifies a numeral, decimal or invalid token, once
	 * a beginning digit is seen.
	 */
	static private class NumberDecimalRule implements IRule {
		private IToken numberToken;
		private IToken decimalToken;
		private IToken invalidToken;
		
		public NumberDecimalRule(IToken numberToken, IToken decimalToken, IToken invalidToken) {
			this.numberToken = numberToken;
			this.decimalToken = decimalToken;
			this.invalidToken = invalidToken;
		}
		
		@Override
		public IToken evaluate(ICharacterScanner scanner) {
			int c = scanner.read();
			if (!Character.isDigit(c)) {
				scanner.unread();
				return Token.UNDEFINED;
			}
			boolean leadingZero = c == '0';
			boolean more = false;
			while (Character.isDigit(c = scanner.read())) {
				more = true;
			}
			if (!more) leadingZero = false;
			if (c != '.') {
				scanner.unread();
				if (leadingZero) return invalidToken;
				return numberToken;
			}
			more = false;
			while (Character.isDigit(c = scanner.read())) { more = true; }
			scanner.unread();
			if (!more || leadingZero) return invalidToken;
			return decimalToken;
		}
		
	}

	/** This detector identifiers a reserved word or unquoted symbol. */
	static private class SymbolRWRule implements IRule {
		private IToken symbolToken;
		private IToken reservedWordToken;
		private Collection<String> reservedWords;
		
		public SymbolRWRule(IToken symbolToken, IToken reservedWordToken, Set<String> reservedWords) {
			this.symbolToken = symbolToken;
			this.reservedWordToken = reservedWordToken;
			this.reservedWords = reservedWords;
		}
		
		@Override
		public IToken evaluate(ICharacterScanner scanner) {
			StringBuilder sb = new StringBuilder();
			int c = scanner.read();
			if (nondigitsymchar.indexOf(c) < 0) {
				scanner.unread();
				return Token.UNDEFINED;
			}
			sb.append((char)c);
			while (symchar.indexOf(c=scanner.read()) >= 0) { sb.append((char)c); }
			scanner.unread();
			if (reservedWords.contains(sb.toString())) return reservedWordToken;
			return symbolToken;
		}
	}
	
	/** This detector identifies binary literals, hex literals, or invalid literals
	 * that begin with #.
	 * @author David R. Cok
	 */
	static private class BinHexRule implements IRule {
		private IToken binToken;
		private IToken hexToken;
		private IToken invalidToken;
		
		public BinHexRule(IToken binToken, IToken hexToken, IToken invalidToken) {
			this.binToken = binToken;
			this.hexToken = hexToken;
			this.invalidToken = invalidToken;
		}
		
		@Override
		public IToken evaluate(ICharacterScanner scanner) {
			int c = scanner.read();
			if (c != '#') {
				scanner.unread();
				return Token.UNDEFINED;
			}
			c = scanner.read();
			int n = 0;
			if (c == 'b') {
				do {
					c = scanner.read();
					++n;
				} while (c == '0' || c == '1');
				scanner.unread();
				if (n == 1) return invalidToken;
				return binToken;
			} else if (c == 'x') {
				do {
					c = scanner.read();
					++n;
				} while ((c>='0'&&c<='9')||(c>='a'&&c<='f')||(c>='A'&&c<='F'));
				scanner.unread();
				if (n == 1) return invalidToken;
				return hexToken;
			} else {
				return invalidToken;
			}
		}
	}
}
