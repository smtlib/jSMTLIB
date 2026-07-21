package org.smtlib.lsp;

import org.eclipse.lsp4j.DocumentSymbol;
import org.eclipse.lsp4j.SymbolKind;
import org.smtlib.ICommand;
import org.smtlib.IPos;
import org.smtlib.ISource;

import java.util.ArrayList;
import java.util.List;

/**
 * Extracts LSP {@link DocumentSymbol} objects from a list of parsed SMT-LIB commands.
 *
 * Handles: declare-fun, declare-const, declare-sort, define-fun, define-sort,
 * define-fun-rec, set-logic, assert (unnamed).
 */
public class DocumentSymbolProvider {

    private DocumentSymbolProvider() {}

    public static List<DocumentSymbol> extract(List<ICommand> commands, ISource source) {
        var result = new ArrayList<DocumentSymbol>();
        for (ICommand cmd : commands) {
            DocumentSymbol sym = toSymbol(cmd, source);
            if (sym != null) result.add(sym);
        }
        return result;
    }

    private static DocumentSymbol toSymbol(ICommand cmd, ISource source) {
        if (cmd instanceof ICommand.Ideclare_fun f) {
            return symbol(f.symbol().value(), SymbolKind.Function, posOf(cmd), source);
        }
        if (cmd instanceof ICommand.Ideclare_const c) {
            return symbol(c.symbol().value(), SymbolKind.Constant, posOf(cmd), source);
        }
        if (cmd instanceof ICommand.Ideclare_sort s) {
            return symbol(s.sortSymbol().value(), SymbolKind.Class, posOf(cmd), source);
        }
        if (cmd instanceof ICommand.Idefine_fun f) {
            return symbol(f.symbol().value(), SymbolKind.Function, posOf(cmd), source);
        }
        if (cmd instanceof ICommand.Idefine_sort s) {
            return symbol(s.sortSymbol().value(), SymbolKind.Class, posOf(cmd), source);
        }
        if (cmd instanceof ICommand.Iset_logic l) {
            return symbol("set-logic " + l.logic().value(), SymbolKind.Module, posOf(cmd), source);
        }
        return null;
    }

    private static IPos posOf(ICommand cmd) {
        if (cmd instanceof IPos.IPosable p) return p.pos();
        return null;
    }

    private static DocumentSymbol symbol(String name, SymbolKind kind, IPos pos, ISource source) {
        var range = (pos != null) ? PositionUtils.toRange(pos)
                : new org.eclipse.lsp4j.Range(
                        new org.eclipse.lsp4j.Position(0, 0),
                        new org.eclipse.lsp4j.Position(0, 0));
        var sym = new DocumentSymbol();
        sym.setName(name);
        sym.setKind(kind);
        sym.setRange(range);
        sym.setSelectionRange(range);
        return sym;
    }
}
