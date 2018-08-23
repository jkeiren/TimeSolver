#ifndef PROVER_OPTIONS_HH
#define PROVER_OPTIONS_HH

/** Structure to collect the options passed to the tool, and passed into the
 * algorithm */
struct prover_options {
  /** True if debug mode is on, and
   * False if debug mode is off. Running the
   * program with -d sets it to true. */
  bool debug;

  /** True if full debug mode is on, and
   * False if full debug mode is off. Running the
   * program with -D sets it to true. */
  bool full_debug;

  /** If True, use tables in the output.  Else (False),
   * print regular output. */
  bool tabled;

  /** The size of the Hash table of Sequents: nBits + 1 */
  unsigned long nHash;

  /** Debug boolean to enable or disable known true and known false caches.
   * This parameter does not influence caching of circularities. As a result,
   * correctness is guaranteed but performance is slowed if set to FALSE */
  bool useCaching;

  prover_options()
      : debug(false), tabled(false), nHash(16), useCaching(true) {}
};

#endif // PROVER_OPTIONS_HH
