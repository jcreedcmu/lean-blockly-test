/**
 * Standalone Lean LSP client using vscode-ws-jsonrpc.
 *
 * Connects a browser WebSocket to a JSON-RPC MessageConnection,
 * sends `initialize` + `initialized`, and returns the connection
 * for callers to use directly.
 */
import { listen } from 'vscode-ws-jsonrpc';

// Derive MessageConnection from listen()'s own type so we always agree
// with the (possibly nested) vscode-jsonrpc that vscode-ws-jsonrpc ships.
type ListenOptions = Parameters<typeof listen>[0];
export type MessageConnection = Parameters<ListenOptions['onConnection']>[0];

/**
 * Open a WebSocket to `wsUrl`, perform LSP `initialize` + `initialized`,
 * and return the live `MessageConnection`.
 */
export function connect(wsUrl: string): Promise<MessageConnection> {
  return new Promise((resolve, reject) => {
    const webSocket = new WebSocket(wsUrl);

    webSocket.onerror = () => {
      reject(new Error(`WebSocket error connecting to ${wsUrl}`));
    };

    listen({
      webSocket,
      onConnection: async (connection) => {
        connection.listen();

        try {
          await connection.sendRequest('initialize', {
            processId: null,
            capabilities: {},
            rootUri: 'file:///',
            initializationOptions: {
              editDelay: 200,
              hasWidgets: true,
            },
          });
          await connection.sendNotification('initialized', {});
          resolve(connection);
        } catch (err) {
          reject(err);
        }
      },
    });
  });
}
