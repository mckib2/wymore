# Wymore System to SCXML Transformation Tools

This directory contains Python scripts to parse Wymore system definitions from Lean 4 files and transform them into SCXML.

## Scripts

- `parser.py`: Contains the `WymoreSystem` AST and the logic to parse Lean 4 `wymore_system` definitions.
- `scxml_transformer.py`: Transforms a `WymoreSystem` object into a pretty-printed SCXML string.
- `batch_transform.py`: A utility script to process multiple Lean files in a directory and save the resulting SCXML files.

## Usage

### Batch Transform
To transform all files in `Appendix3/` and save them to `output_scxml/`:
```bash
python3 scripts/batch_transform.py -i Appendix3 -o output_scxml
```

### Single File Transform
To transform a single file and print to stdout:
```bash
python3 scripts/scxml_transformer.py Appendix3/Zx1.lean
```

To transform and save to a file:
```bash
python3 scripts/scxml_transformer.py Appendix3/Zx1.lean -o Zx1.scxml
```

## Requirements
- Python 3.x (uses standard libraries: `re`, `ast`, `xml.etree.ElementTree`, `xml.dom.minidom`, `glob`, `os`).
