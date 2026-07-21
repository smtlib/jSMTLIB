package org.smtlib.lsp;

import org.eclipse.lsp4j.Position;
import org.eclipse.lsp4j.Range;
import org.smtlib.IPos;
import org.smtlib.ISource;

/**
 * Converts jSMTLIB {@link IPos} values to LSP {@link Position}/{@link Range}.
 *
 * LSP positions are 0-based (line and character).
 * ISource.lineNumber() returns 1-based line numbers.
 * Column = charOffset - ISource.lineBeginning(charOffset).
 */
public class PositionUtils {

    private PositionUtils() {}

    public static Position toPosition(ISource source, int charOffset) {
        if (source == null) return new Position(0, 0);
        int line   = source.lineNumber(charOffset) - 1;  // 0-based
        int col    = charOffset - source.lineBeginning(charOffset);
        return new Position(Math.max(0, line), Math.max(0, col));
    }

    public static Range toRange(IPos pos) {
        if (pos == null || pos.source() == null) return new Range(new Position(0, 0), new Position(0, 0));
        ISource src   = pos.source();
        Position start = toPosition(src, pos.charStart());
        Position end   = toPosition(src, pos.charEnd());
        return new Range(start, end);
    }

    /** Returns a zero-width range at a given character offset (useful for errors without extent). */
    public static Range pointRange(ISource source, int charOffset) {
        Position p = toPosition(source, charOffset);
        return new Range(p, p);
    }
}
