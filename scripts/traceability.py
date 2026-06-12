#!/usr/bin/env python3
import os
import re
import sys
import json
import argparse

# Regex to find textbook definition/theorem tags: e.g., [textbook/definition2.4/component/SZ] or [textbook/theorem2.25/theorem/translation_closed]
TAG_RE = re.compile(r'\[(textbook/[0-9a-zA-Z\.\-_]+(?:/[a-zA-Z0-9\.\-_/]+)?)\]')

# Path config
WORKSPACE_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEAN_DIRS = ['Mbse', 'Appendix3']
TEXTBOOK_DIR = os.path.join(WORKSPACE_DIR, 'textbook')

def load_textbook_definitions():
    definitions = {}
    if not os.path.isdir(TEXTBOOK_DIR):
        return definitions
        
    for file in os.listdir(TEXTBOOK_DIR):
        if file.endswith('.json'):
            filepath = os.path.join(TEXTBOOK_DIR, file)
            try:
                with open(filepath, 'r', encoding='utf-8') as f:
                    data = json.load(f)
                    def_key = f"textbook/{os.path.splitext(file)[0]}"
                    definitions[def_key] = data
            except Exception as e:
                print(f"Error reading JSON definition {file}: {e}", file=sys.stderr)
    return definitions

def parse_lean_files(definitions):
    traceability_map = {}
    # Structure: { base_def_key: { element_id: [lean_items] } }
    
    # Initialize all JSON elements with empty trace lists
    for def_key, def_data in definitions.items():
        traceability_map[def_key] = {elem['id']: [] for elem in def_data.get('elements', [])}
        
    lean_to_textbook = {}
    
    # Regexes to extract declaration names from Lean code
    def_name_re = re.compile(r'\b(?:def|theorem|lemma|structure|abbrev|inductive|class)\s+([a-zA-Z0-9_]+)')
    field_re = re.compile(r'^\s+([a-zA-Z0-9_]+)\s*:')

    for folder in LEAN_DIRS:
        folder_path = os.path.join(WORKSPACE_DIR, folder)
        if not os.path.isdir(folder_path):
            continue
            
        for root, _, files in os.walk(folder_path):
            for file in files:
                if not file.endswith('.lean'):
                    continue
                
                filepath = os.path.join(root, file)
                rel_path = os.path.relpath(filepath, WORKSPACE_DIR)
                
                with open(filepath, 'r', encoding='utf-8') as f:
                    lines = f.readlines()
                    
                # Stateful parsing
                in_docstring = False
                docstring_lines = []
                structure_name = None
                structure_indent = None
                
                for idx, line in enumerate(lines):
                    line_num = idx + 1
                    stripped = line.strip()
                    
                    # Detect structure blocks to identify fields
                    if not in_docstring:
                        struct_match = re.search(r'\bstructure\s+([a-zA-Z0-9_]+)', line)
                        if struct_match:
                            structure_name = struct_match.group(1)
                            structure_indent = len(line) - len(line.lstrip())
                        elif structure_name and line.startswith(' ' * (structure_indent or 0)):
                            if stripped == 'end' or (stripped and not line.startswith(' ') and not line.startswith('--') and not line.startswith('/-')):
                                structure_name = None
                                structure_indent = None
                    
                    # Manage docstrings
                    if stripped.startswith('/--'):
                        in_docstring = True
                        docstring_lines = [line]
                        if stripped.endswith('-/'):
                            in_docstring = False
                            process_docstring(docstring_lines, lines, idx, rel_path, line_num, structure_name, definitions, traceability_map, lean_to_textbook, def_name_re, field_re)
                        continue
                    elif in_docstring:
                        docstring_lines.append(line)
                        if stripped.endswith('-/'):
                            in_docstring = False
                            process_docstring(docstring_lines, lines, idx, rel_path, idx + 2 - len(docstring_lines), structure_name, definitions, traceability_map, lean_to_textbook, def_name_re, field_re)
                        continue
                    
                    # Inline comments
                    inline_tags = TAG_RE.findall(line)
                    if inline_tags and not in_docstring:
                        item_name = "Unknown"
                        item_type = "comment"
                        
                        peek_idx = idx
                        while peek_idx < len(lines) - 1 and peek_idx < idx + 3:
                            peek_idx += 1
                            peek_line = lines[peek_idx].strip()
                            if peek_line and not peek_line.startswith('--') and not peek_line.startswith('/-'):
                                code_match = def_name_re.search(peek_line)
                                if code_match:
                                    item_name = code_match.group(1)
                                    item_type = "code"
                                    break
                                elif structure_name and field_re.match(lines[peek_idx]):
                                    item_name = f"{structure_name}.{field_re.match(lines[peek_idx]).group(1)}"
                                    item_type = "field"
                                    break
                        
                        for tag in inline_tags:
                            add_trace(tag, item_name, rel_path, line_num, item_type, stripped, definitions, traceability_map, lean_to_textbook)

    return traceability_map, lean_to_textbook

def process_docstring(docstring_lines, all_lines, end_idx, rel_path, start_line_num, structure_name, definitions, traceability_map, lean_to_textbook, def_name_re, field_re):
    docstring_text = "".join(docstring_lines)
    tags = TAG_RE.findall(docstring_text)
    if not tags:
        return
        
    item_name = "Unknown"
    item_type = "unknown"
    
    peek_idx = end_idx + 1
    while peek_idx < len(all_lines):
        next_line = all_lines[peek_idx]
        next_stripped = next_line.strip()
        if not next_stripped or next_stripped.startswith('--') or next_stripped.startswith('/-'):
            peek_idx += 1
            continue
            
        code_match = def_name_re.search(next_line)
        if code_match:
            item_name = code_match.group(1)
            item_type = "code"
            break
        elif structure_name and field_re.match(next_line):
            item_name = f"{structure_name}.{field_re.match(next_line).group(1)}"
            item_type = "field"
            break
        else:
            item_name = next_stripped
            item_type = "statement"
            break
            
    for tag in tags:
        add_trace(tag, item_name, rel_path, start_line_num, item_type, docstring_text, definitions, traceability_map, lean_to_textbook)

def add_trace(tag, item_name, rel_path, line_num, item_type, content, definitions, traceability_map, lean_to_textbook):
    # Parse tag structure, e.g. textbook/definition2.4/component/SZ
    parts = tag.split('/')
    if len(parts) < 3:
        # Backward compatibility or fallback
        base_def_key = tag
        element_suffix = None
    else:
        base_def_key = f"{parts[0]}/{parts[1]}"
        element_suffix = "/".join(parts[2:])
        
    record = {
        'item': item_name,
        'file': rel_path,
        'line': line_num,
        'type': item_type,
        'raw_tag': tag
    }
    
    if base_def_key not in traceability_map:
        traceability_map[base_def_key] = {}
        
    # Match the element in JSON definition
    matched_element_id = None
    if base_def_key in definitions:
        for elem in definitions[base_def_key].get('elements', []):
            elem_id = elem['id']
            if element_suffix and (elem_id == element_suffix or elem_id.endswith(element_suffix)):
                matched_element_id = elem_id
                break
                
    if not matched_element_id:
        # Fallback to suffix key if no JSON element matched
        matched_element_id = element_suffix or "general"
        
    if matched_element_id not in traceability_map[base_def_key]:
        traceability_map[base_def_key][matched_element_id] = []
        
    traceability_map[base_def_key][matched_element_id].append(record)
    
    fullname = f"{rel_path}#{line_num} ({item_name})"
    if fullname not in lean_to_textbook:
        lean_to_textbook[fullname] = []
    lean_to_textbook[fullname].append((tag, matched_element_id))

def generate_markdown_report(definitions, traceability_map):
    report_path = os.path.join(WORKSPACE_DIR, 'traceability_report.md')
    
    with open(report_path, 'w', encoding='utf-8') as f:
        f.write("# Bidirectional Traceability Report (Structured)\n\n")
        f.write("> [!NOTE]\n")
        f.write("> This report is auto-generated by `scripts/traceability.py` to verify mapping completeness between Lean 4 implementations and Wayne Wymore's structured textbook definitions.\n\n")
        
        f.write("## 1. Textbook Definitions Mapping & Coverage\n\n")
        
        total_elements = 0
        traced_elements = 0
        
        for def_key in sorted(definitions.keys()):
            def_data = definitions[def_key]
            def_filename = def_key.split('/')[-1]
            json_rel_path = f"textbook/{def_filename}.json"
            
            f.write(f"### `{def_key}` — {def_data.get('name', 'Unnamed Definition')}\n\n")
            f.write(f"- Structured source file: [{json_rel_path}](file://{os.path.join(TEXTBOOK_DIR, def_filename + '.json')})\n")
            f.write(f"- Description: *{def_data.get('description', '')}*\n\n")
            
            f.write("| Element ID | Type | Textbook Text | Status | Linked Lean Elements |\n")
            f.write("|------------|------|---------------|--------|----------------------|\n")
            
            elements = def_data.get('elements', [])
            trace_data = traceability_map.get(def_key, {})
            
            for elem in elements:
                elem_id = elem['id']
                elem_type = elem.get('type', 'unknown')
                elem_text = elem.get('text', '')
                
                links = trace_data.get(elem_id, [])
                total_elements += 1
                
                if links:
                    traced_elements += 1
                    status_str = "✅ Traced"
                    link_strs = []
                    for link in links:
                        link_loc = f"[{link['file']}:{link['line']}](file://{os.path.join(WORKSPACE_DIR, link['file'])}#L{link['line']})"
                        link_strs.append(f"`{link['item']}` ({link_loc})")
                    links_str = "<br>".join(link_strs)
                else:
                    status_str = "❌ Untraced"
                    links_str = "*None (Coverage Gap)*"
                    
                f.write(f"| `{elem_id}` | `{elem_type}` | {elem_text} | {status_str} | {links_str} |\n")
            f.write("\n")
            
        f.write("## 2. Completeness & Quality Summary\n\n")
        if total_elements > 0:
            coverage = (traced_elements / total_elements) * 100
        else:
            coverage = 0.0
            
        f.write(f"- **Total Structured Definitions Tracked**: {len(definitions)}\n")
        f.write(f"- **Total Individual Requirements/Elements**: {total_elements}\n")
        f.write(f"- **Traced/Formalized Elements**: {traced_elements} ({traced_elements}/{total_elements})\n")
        f.write(f"- **Formalization Coverage Rate**: **{coverage:.1f}%**\n")
        
        if coverage == 100.0:
            f.write("\n> [!TIP]\n> 🎉 **100% Traceability and Coverage achieved!** All defined elements, constraints, and implications in the structured textbook specifications have matching formalized items in Lean.")
        else:
            f.write("\n> [!WARNING]\n> There are coverage gaps between the textbook specification and the Lean implementation. See the table(s) above to find untraced requirements.")

    print(f"Generated report at: {report_path}")

def run_verify(definitions, traceability_map):
    print("=== Verification Check ===")
    gaps = 0
    
    for def_key, def_data in definitions.items():
        print(f"\nChecking definition: {def_key} ({def_data.get('name')})")
        elements = def_data.get('elements', [])
        trace_data = traceability_map.get(def_key, {})
        
        for elem in elements:
            elem_id = elem['id']
            links = trace_data.get(elem_id, [])
            if not links:
                print(f" ❌ Missing Lean link for element: `{elem_id}` ({elem.get('type')}) - \"{elem.get('text')}\"")
                gaps += 1
            else:
                print(f" ✅ Traced element: `{elem_id}` to {len(links)} Lean item(s).")
                
    print(f"\nVerification complete. Found {gaps} coverage gaps/untraced requirements.")
    return gaps

def main():
    parser = argparse.ArgumentParser(description="Structured MBSE Traceability Utility")
    parser.add_argument('--report', action='store_true', help="Generate Markdown Traceability Report")
    parser.add_argument('--query', type=str, help="Query elements for a specific textbook definition (e.g. textbook/definition2.4)")
    parser.add_argument('--explain', type=str, help="Explain textbook source for a Lean element name")
    parser.add_argument('--verify', action='store_true', help="Verify that all definitions link correctly and check coverage")
    
    args = parser.parse_args()
    
    definitions = load_textbook_definitions()
    trace_map, lean_map = parse_lean_files(definitions)
    
    if args.report:
        generate_markdown_report(definitions, trace_map)
        
    if args.query:
        query_def = args.query.strip()
        if query_def in trace_map:
            print(f"\nStructured elements for `{query_def}`:")
            def_data = definitions.get(query_def, {})
            elements_dict = {e['id']: e for e in def_data.get('elements', [])}
            
            for elem_id, links in trace_map[query_def].items():
                elem_info = elements_dict.get(elem_id, {})
                type_str = elem_info.get('type', 'unknown')
                text_str = elem_info.get('text', '')
                
                print(f"\n* Element: `{elem_id}` [{type_str}]")
                print(f"  Text: \"{text_str}\"")
                if links:
                    print(f"  Traced in Lean:")
                    for link in links:
                        print(f"   - {link['file']}:{link['line']} ({link['item']})")
                else:
                    print(f"  Status: ❌ Untraced (Coverage Gap)")
        else:
            print(f"No elements found for textbook definition: `{query_def}`")
            
    if args.explain:
        elem_name = args.explain.strip()
        found = False
        for def_key, trace_data in trace_map.items():
            def_data = definitions.get(def_key, {})
            elements_dict = {e['id']: e for e in def_data.get('elements', [])}
            
            for elem_id, links in trace_data.items():
                for link in links:
                    if link['item'] == elem_name or link['item'].endswith(f".{elem_name}"):
                        elem_info = elements_dict.get(elem_id, {})
                        print(f"\nTraceability Justification:")
                        print(f" - Lean element: `{link['item']}` (defined at {link['file']}:{link['line']})")
                        print(f" - Maps to textbook definition: `{def_key}`")
                        print(f" - Sub-element ID: `{elem_id}`")
                        print(f" - Element Type: `{elem_info.get('type')}`")
                        print(f" - Requirement Text: \"{elem_info.get('text')}\"")
                        found = True
        if not found:
            print(f"Could not find any traceability justification for Lean element: `{elem_name}`")
            
    if args.verify:
        run_verify(definitions, trace_map)
        
    if not (args.report or args.query or args.explain or args.verify):
        generate_markdown_report(definitions, trace_map)
        run_verify(definitions, trace_map)

if __name__ == '__main__':
    main()
