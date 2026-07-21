package org.smtlib.lsp.test;

import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.TimeUnit;

/**
 * Minimal synchronous JSON-RPC client for over-the-wire LSP protocol testing.
 *
 * Writes and reads raw Content-Length-framed JSON messages directly, exercising
 * the server's full JSON-RPC receive / process / respond path without using
 * LSP4J's client-side serialization.
 *
 * Notifications (messages with "method" and no "id") are queued and retrieved via
 * {@link #nextNotification}.  Responses (messages with "id" and no "method") are
 * queued and retrieved via {@link #nextResponse}.
 */
public class RawLspClient {

    private final OutputStream out;
    private final InputStream  in;
    private int nextId = 1;

    private final BlockingQueue<JsonObject> notifications = new LinkedBlockingQueue<>();
    private final BlockingQueue<JsonObject> responses     = new LinkedBlockingQueue<>();

    private final Thread reader;
    private volatile boolean running = true;

    public RawLspClient(OutputStream serverInput, InputStream serverOutput) {
        this.out = serverInput;
        this.in  = serverOutput;

        reader = new Thread(() -> {
            while (running) {
                try {
                    String raw = readMessage();
                    if (raw == null) break;
                    JsonObject msg = JsonParser.parseString(raw).getAsJsonObject();
                    if (msg.has("method") && !msg.has("id")) {
                        notifications.offer(msg);
                    } else if (msg.has("id") && !msg.has("method")) {
                        responses.offer(msg);
                    }
                    // Server-to-client requests (have both "id" and "method") are ignored.
                } catch (IOException e) {
                    break;
                }
            }
        }, "RawLspClient-reader");
        reader.setDaemon(true);
        reader.start();
    }

    /**
     * Send a JSON-RPC request with an auto-assigned id.
     *
     * @return the id assigned (pass to {@link #nextResponse} to read the reply)
     */
    public int sendRequest(String method, String params) throws IOException {
        int id = nextId++;
        String body = params == null
                ? "{\"jsonrpc\":\"2.0\",\"id\":" + id + ",\"method\":\"" + method + "\"}"
                : "{\"jsonrpc\":\"2.0\",\"id\":" + id + ",\"method\":\"" + method + "\",\"params\":" + params + "}";
        writeMessage(body);
        return id;
    }

    /** Send a JSON-RPC notification (no id, no response expected). */
    public void sendNotification(String method, String params) throws IOException {
        String body = params == null
                ? "{\"jsonrpc\":\"2.0\",\"method\":\"" + method + "\"}"
                : "{\"jsonrpc\":\"2.0\",\"method\":\"" + method + "\",\"params\":" + params + "}";
        writeMessage(body);
    }

    /**
     * Wait for the next server response. Responses arrive in send order.
     *
     * @return the full response JSON, or {@code null} on timeout
     */
    public JsonObject nextResponse(long timeout, TimeUnit unit) throws InterruptedException {
        return responses.poll(timeout, unit);
    }

    /**
     * Wait for the next notification with the given method name.
     * Discards notifications with other methods while waiting.
     *
     * @return the notification JSON, or {@code null} on timeout
     */
    public JsonObject nextNotification(String method, long timeout, TimeUnit unit)
            throws InterruptedException {
        long deadline = System.nanoTime() + unit.toNanos(timeout);
        while (true) {
            long remaining = deadline - System.nanoTime();
            if (remaining <= 0) return null;
            JsonObject msg = notifications.poll(remaining, TimeUnit.NANOSECONDS);
            if (msg == null) return null;
            if (method.equals(msg.get("method").getAsString())) return msg;
        }
    }

    public void stop() {
        running = false;
        reader.interrupt();
    }

    // -----------------------------------------------------------------------
    // Content-Length framing
    // -----------------------------------------------------------------------

    private void writeMessage(String body) throws IOException {
        byte[] bytes = body.getBytes(StandardCharsets.UTF_8);
        String header = "Content-Length: " + bytes.length + "\r\n\r\n";
        synchronized (out) {
            out.write(header.getBytes(StandardCharsets.US_ASCII));
            out.write(bytes);
            out.flush();
        }
    }

    private String readMessage() throws IOException {
        int contentLength = -1;
        while (true) {
            String line = readLine();
            if (line == null) return null;    // EOF
            if (line.isEmpty()) break;         // blank line ends headers
            if (line.startsWith("Content-Length:"))
                contentLength = Integer.parseInt(line.substring("Content-Length:".length()).trim());
        }
        if (contentLength < 0) return null;

        byte[] buf = new byte[contentLength];
        int read = 0;
        while (read < contentLength) {
            int n = in.read(buf, read, contentLength - read);
            if (n < 0) return null;
            read += n;
        }
        return new String(buf, StandardCharsets.UTF_8);
    }

    /** Read a CRLF-terminated line; returns {@code null} on EOF. */
    private String readLine() throws IOException {
        StringBuilder sb = new StringBuilder();
        int prev = -1;
        while (true) {
            int b = in.read();
            if (b < 0) return sb.length() == 0 ? null : sb.toString();
            if (b == '\n' && prev == '\r') {
                sb.setLength(sb.length() - 1);
                return sb.toString();
            }
            sb.append((char) b);
            prev = b;
        }
    }
}
