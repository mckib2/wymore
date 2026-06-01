import xml.etree.ElementTree as ET
from xml.dom import minidom
from parser import WymoreSystem, parse_wymore_system
import re

def sanitize_id(obj) -> str:
    """Convert an arbitrary Python object (number, tuple, etc.) to a valid XML ID."""
    s = str(obj)
    # Replace non-alphanumeric with underscore
    s = re.sub(r'[^a-zA-Z0-9]', '_', s)
    # Ensure it starts with a letter
    if not s[0].isalpha():
        s = 's' + s
    # Remove double underscores
    s = re.sub(r'_+', '_', s)
    return s.strip('_')

def system_to_scxml(system: WymoreSystem) -> str:
    root = ET.Element('scxml', {
        'xmlns': 'http://www.w3.org/2005/07/scxml',
        'version': '1.0',
        'initial': sanitize_id(list(system.states)[0]) if system.states else ""
    })

    # Sort states for deterministic output
    sorted_states = sorted(list(system.states), key=lambda x: str(x))

    for state in sorted_states:
        state_id = sanitize_id(state)
        state_elem = ET.SubElement(root, 'state', {'id': state_id})
        
        # Add readout (output) as a comment or onentry log
        if state in system.readout:
            output_val = system.readout[state]
            onentry = ET.SubElement(state_elem, 'onentry')
            # Using log as a simple way to represent output in SCXML
            ET.SubElement(onentry, 'log', {'label': 'output', 'expr': f"'{str(output_val)}'"})

        # Add transitions
        # Transitions are (state, input) -> next_state
        # Find all transitions for this state
        for (s, inp), next_s in system.transitions.items():
            if s == state:
                ET.SubElement(state_elem, 'transition', {
                    'event': sanitize_id(inp),
                    'target': sanitize_id(next_s)
                })

    # Use minidom for pretty printing
    xml_str = ET.tostring(root, encoding='utf-8')
    pretty_xml = minidom.parseString(xml_str).toprettyxml(indent="  ")
    return pretty_xml

if __name__ == "__main__":
    import argparse
    
    parser = argparse.ArgumentParser(description="Transform a Lean 4 Wymore system definition to SCXML.")
    parser.add_argument("input", help="Path to the .lean file containing the wymore_system definition.")
    parser.add_argument("-o", "--output", help="Path to save the generated SCXML. If not provided, output is printed to stdout.")
    
    args = parser.parse_args()

    try:
        with open(args.input, 'r') as f:
            content = f.read()
            system = parse_wymore_system(content)
            scxml = system_to_scxml(system)
            
            if args.output:
                with open(args.output, 'w') as out_f:
                    out_f.write(scxml)
                print(f"Successfully wrote SCXML to {args.output}")
            else:
                print(scxml)
    except Exception as e:
        print(f"Error: {e}")
        exit(1)
