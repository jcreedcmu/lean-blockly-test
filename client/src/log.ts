const t0 = Date.now();
function elapsed(): string { return `+${((Date.now() - t0) / 1000).toFixed(1)}s`; }

export function log(category: string, message: string, ...args: unknown[]): void {
  console.log(`[${category} ${elapsed()}] ${message}`, ...args);
}

export function logError(category: string, message: string, ...args: unknown[]): void {
  console.error(`[${category} ${elapsed()}] ${message}`, ...args);
}
