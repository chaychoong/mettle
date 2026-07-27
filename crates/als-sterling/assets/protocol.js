/**
 * The Sterling provider protocol, client side (`docs/reference/sterling.md`
 * §2), plus the two things mettle's own provider adds to it (ADR-0016
 * Decision 2 amendments): the `error` message type, and the optional `state`
 * field on a `click`.
 *
 * The connection owns three concerns and nothing else — framing, keepalive,
 * and reconnection — so the app above it never sees a socket. Requests are
 * answered in order on one socket, which is what lets `evaluate()` be a
 * promise keyed by its own expression id and `click()` be fire-and-forget: the
 * `data` or `error` that answers a click is delivered to the same handlers a
 * spontaneous refresh would use, because they are indistinguishable and the
 * app treats them the same way.
 */

const VERSION = 1;

/** §2.1: the upstream client's own keepalive cadence, in ms. */
const PING_INTERVAL_MS = 3000;

/**
 * No frame of any kind for this long means the socket is wedged rather than
 * idle — every ping is answered with a `pong` within a round trip on
 * loopback, so silence past three of them is a dead connection the browser has
 * not noticed yet.
 */
const SILENCE_LIMIT_MS = 10000;

/** §2.1: the upstream client's own reconnect interval, in ms. */
const RECONNECT_DELAY_MS = 1000;

/**
 * Opens the provider socket and keeps it open.
 *
 * `handlers` takes `onStatus(state)` (`connecting`/`connected`/`reconnecting`),
 * `onDatum(datum)` for each entering datum, `onMeta(meta)`, and
 * `onError({code, message})` for the provider's typed refusals.
 */
export function connectProvider(url, handlers) {
  let socket = null;
  let pingTimer = null;
  let watchdog = null;
  let closed = false;
  let nextExpressionId = 0;
  const pending = new Map();

  function open() {
    handlers.onStatus(socket === null ? 'connecting' : 'reconnecting');
    socket = new WebSocket(url);
    socket.addEventListener('open', () => {
      handlers.onStatus('connected');
      send({ type: 'meta', version: VERSION });
      send({ type: 'data', version: VERSION });
      pingTimer = setInterval(() => sendRaw('ping'), PING_INTERVAL_MS);
      touch();
    });
    socket.addEventListener('message', (event) => {
      touch();
      receive(event.data);
    });
    socket.addEventListener('close', () => reopen());
    // An error is always followed by a close; the close path is the one that
    // schedules the retry, so this only needs to not be silent.
    socket.addEventListener('error', () => handlers.onStatus('reconnecting'));
  }

  function reopen() {
    clearTimers();
    for (const [, settle] of pending) settle.reject(new Error('the provider connection dropped'));
    pending.clear();
    if (closed) return;
    handlers.onStatus('reconnecting');
    setTimeout(open, RECONNECT_DELAY_MS);
  }

  /** Restarts the silence watchdog; any received frame counts as liveness. */
  function touch() {
    clearTimeout(watchdog);
    watchdog = setTimeout(() => {
      // Closing here is what turns a wedged socket into a reconnect: the
      // `close` handler is the only place retries are scheduled.
      if (socket !== null) socket.close();
    }, SILENCE_LIMIT_MS);
  }

  function clearTimers() {
    clearInterval(pingTimer);
    clearTimeout(watchdog);
    pingTimer = null;
    watchdog = null;
  }

  function receive(frame) {
    if (typeof frame !== 'string') return;
    if (frame === 'pong') return;
    let message;
    try {
      message = JSON.parse(frame);
    } catch {
      handlers.onError({ code: 'malformed-reply', message: 'the provider sent a frame that is not JSON.' });
      return;
    }
    const payload = message.payload ?? {};
    switch (message.type) {
      case 'data':
        for (const datum of payload.enter ?? []) handlers.onDatum(datum);
        break;
      case 'meta':
        handlers.onMeta(payload);
        break;
      case 'eval': {
        const settle = pending.get(payload.id);
        if (settle !== undefined) {
          pending.delete(payload.id);
          settle.resolve(payload.result ?? '');
        }
        break;
      }
      // mettle's fifth type. An upstream Sterling ignores it; this frontend is
      // the client it exists for.
      case 'error':
        handlers.onError({ code: payload.code ?? 'error', message: payload.message ?? '' });
        break;
      default:
        break;
    }
  }

  function sendRaw(frame) {
    if (socket === null || socket.readyState !== WebSocket.OPEN) return false;
    socket.send(frame);
    return true;
  }

  function send(message) {
    return sendRaw(JSON.stringify(message));
  }

  return {
    /** Asks for the current datum again (after a reconnect, or a manual refresh). */
    requestData() {
      return send({ type: 'data', version: VERSION });
    },

    /**
     * Fires a provider-defined action. `state` is mettle's optional extension:
     * the displayed state index a `new-fork` should fork after. It is sent
     * only when the caller has one — omitting it leaves the provider on its
     * evaluator-pane fallback, which is what an external client gets.
     */
    click(datumId, onClick, state) {
      const payload = { id: datumId, onClick };
      if (state !== undefined && state !== null) payload.state = state;
      return send({ type: 'click', version: VERSION, payload });
    },

    /** Evaluates one expression against `datumId`, resolving with the provider's rendered answer. */
    evaluate(datumId, expression) {
      const id = `e${nextExpressionId}`;
      nextExpressionId += 1;
      return new Promise((resolve, reject) => {
        pending.set(id, { resolve, reject });
        const sent = send({ type: 'eval', version: VERSION, payload: { id, datumId, expression } });
        if (!sent) {
          pending.delete(id);
          reject(new Error('not connected to the provider'));
        }
      });
    },

    /** Stops reconnecting — the page is going away. */
    close() {
      closed = true;
      clearTimers();
      if (socket !== null) socket.close();
    },

    start: open,
  };
}
