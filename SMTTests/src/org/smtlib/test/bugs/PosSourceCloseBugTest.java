package org.smtlib.test.bugs;

import java.util.concurrent.TimeUnit;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.impl.Pos;

/**
 * Pins down impl/Pos.java's {@code Source} class (around lines 87-91, 106-109, 139-144): the
 * {@code CharSequence}-backed constructor ({@code Source(CharSequence cs, Object location)})
 * never sets the {@code rdr} field (it stays {@code null}), but {@code close()} unconditionally
 * calls {@code rdr.close()}:
 *
 * <pre>public Source(CharSequence cs, /*@Nullable*&#47; Object location) {
 *     this.chars = cs;
 *     this.location = location;
 * }
 * ...
 * public void close() {
 *     try {
 *         rdr.close();
 *     } catch (IOException e) {}
 * }</pre>
 *
 * Currently dormant -- no call site in this codebase closes a {@code Source} built this way
 * -- but {@code APIExample.java} demonstrates exactly this construction pattern
 * ({@code createSource(CharSequence, location)}), so the moment a caller follows that
 * example and calls {@code .close()}, it throws {@code NullPointerException} instead of
 * simply being a no-op (there being no {@code Reader} to close for a CharSequence-backed
 * source).
 * <p>
 * Asserts the correct behavior: closing a CharSequence-backed Source should be a no-op. This
 * currently FAILS against today's code (NullPointerException instead), documenting the bug.
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/74">issue #74</a>.
 * <p>
 * Stays a JUnit test: as the class doc already notes, no call site in this codebase ever
 * closes a {@code CharSequence}-backed {@code Source} -- it's reachable only via direct API
 * use (as {@code APIExample.java} demonstrates), never through any CLI-driven script.
 */
public class PosSourceCloseBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    @Test
    public void closingACharSequenceBackedSourceIsANoOp() throws Exception {
        Pos.Source source = new Pos.Source("(assert true)", "in-memory");
        source.close();
    }
}
