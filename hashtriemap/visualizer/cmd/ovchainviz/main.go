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
		inputPath  string
		outputPath string
		format     string
	)
	flag.StringVar(&inputPath, "in", "", "path to the JSON trace file (default: stdin)")
	flag.StringVar(&outputPath, "out", "", "path to write the rendered output (default: stdout)")
	flag.StringVar(&format, "format", "html", "output format: html, graph-html, animated-html, or json")
	flag.Parse()

	trace, err := readTrace(inputPath)
	if err != nil {
		die(err)
	}

	var out []byte
	switch format {
	case "html":
		out, err = pkg.RenderOvChainTraceHTML(trace)
	case "graph-html", "animated-html":
		out, err = pkg.RenderOvChainTraceGraphHTML(trace)
	case "json":
		var result *pkg.OvChainTraceResult
		result, err = pkg.SimulateOvChainTrace(trace)
		if err == nil {
			out, err = json.MarshalIndent(result, "", "  ")
			if err == nil {
				out = append(out, '\n')
			}
		}
	default:
		die(fmt.Errorf("unsupported format %q", format))
	}
	if err != nil {
		die(err)
	}
	if err := writeOutput(outputPath, out); err != nil {
		die(err)
	}
}

func readTrace(path string) (pkg.OvChainTrace, error) {
	var (
		trace pkg.OvChainTrace
		file  *os.File
		err   error
	)
	if path == "" {
		file = os.Stdin
	} else {
		file, err = os.Open(path)
		if err != nil {
			return trace, err
		}
		defer file.Close()
	}
	decoder := json.NewDecoder(file)
	decoder.DisallowUnknownFields()
	if err := decoder.Decode(&trace); err != nil {
		return trace, err
	}
	return trace, nil
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
