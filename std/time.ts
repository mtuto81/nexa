// Bundled monotonic clock for elapsed-time measurements.

extern "C" {
  function nexa_time_now_ms(): number;
}

export function nowMs(): number {
  return unsafe { nexa_time_now_ms() };
}
