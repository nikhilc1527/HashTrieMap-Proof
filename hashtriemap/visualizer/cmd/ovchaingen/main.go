package main

import (
	"encoding/json"
	"flag"
	"fmt"
	"os"

	pkg "hashtriemap/visualizer"
)

func main() {
	var (
		outputPath         string
		seed               int64
		threads            int
		opsPerThread       int
		keySpace           int
		valueSpace         int
		maxBurst           int
		maxYieldDecisions  int
		blockedStepChance  float64
		title              string
	)
	flag.StringVar(&outputPath, "out", "", "path to write the generated JSON trace (default: stdout)")
	flag.Int64Var(&seed, "seed", 0, "random seed; 0 uses the current time")
	flag.IntVar(&threads, "threads", 3, "number of concurrent threads to generate")
	flag.IntVar(&opsPerThread, "ops", 6, "number of operations to generate per thread")
	flag.IntVar(&keySpace, "keys", 6, "number of distinct keys used by the generator")
	flag.IntVar(&valueSpace, "values", 100, "range of generated values [0, values)")
	flag.IntVar(&maxBurst, "max-burst", 4, "maximum preferred run length for one thread before switching")
	flag.IntVar(&maxYieldDecisions, "max-yield", 4, "maximum number of explicit yield decisions for Range/AllIterate")
	flag.Float64Var(&blockedStepChance, "blocked-chance", 0.18, "probability of emitting a blocked lock-attempt step when possible")
	flag.StringVar(&title, "title", "", "trace title; default embeds the chosen seed")
	flag.Parse()

	trace, err := pkg.GenerateRandomOvChainTrace(pkg.OvChainRandomTraceOptions{
		Seed:              seed,
		Title:             title,
		Threads:           threads,
		OpsPerThread:      opsPerThread,
		KeySpace:          keySpace,
		ValueSpace:        valueSpace,
		MaxBurst:          maxBurst,
		MaxYieldDecisions: maxYieldDecisions,
		BlockedStepChance: blockedStepChance,
	})
	if err != nil {
		die(err)
	}
	out, err := json.MarshalIndent(trace, "", "  ")
	if err != nil {
		die(err)
	}
	out = append(out, '\n')
	if err := writeOutput(outputPath, out); err != nil {
		die(err)
	}
}

func writeOutput(path string, data []byte) error {
	if path == "" {
		_, err := os.Stdout.Write(data)
		return err
	}
	return os.WriteFile(path, data, 0o644)
}

func die(err error) {
	fmt.Fprintln(os.Stderr, err)
	os.Exit(1)
}
