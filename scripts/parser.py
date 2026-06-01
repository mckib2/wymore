import re
import ast
from typing import Set, Dict, Tuple, Any

class WymoreSystem:
    def __init__(self, name: str, states: Set, inputs: Set, outputs: Set, transitions: Dict[Tuple[Any, Any], Any], readout: Dict[Any, Any]):
        self.name = name
        self.states = states
        self.inputs = inputs
        self.outputs = outputs
        self.transitions = transitions  # (state, input) -> next_state
        self.readout = readout          # state -> output

    def __repr__(self):
        return f"WymoreSystem(name={self.name}, states={self.states}, inputs={self.inputs}, outputs={self.outputs})"

def parse_lean_set(set_str: str) -> Set:
    # Remove leading/trailing braces and whitespace
    set_str = set_str.strip()
    if not (set_str.startswith('{') and set_str.endswith('}')):
        raise ValueError(f"Invalid set format: {set_str}")
    
    # Python's literal_eval handles sets and tuples nicely
    # However, empty set in Lean is {} which is empty dict in Python.
    # We should handle that.
    if set_str == '{}':
        return set()
    
    # literal_eval expects commas between elements.
    # Lean seems to use commas too.
    return ast.literal_eval(set_str)

def parse_wymore_system(content: str) -> WymoreSystem:
    # Find the wymore_system definition
    # Example: wymore_system Zx1 = (SZx1, IZx1, OZx1, NZx1, RZx1) where
    match = re.search(r'wymore_system\s+(\w+)\s*=', content)
    if not match:
        raise ValueError("Could not find wymore_system definition")
    
    name = match.group(1)
    
    # Extract sets
    # Pattern to match: Key = { ... }
    # We need to be careful with nested braces if they existed, but here only sets have braces.
    # However, tuples have parens.
    
    sets = {}
    # Find all X = { ... } patterns
    # We use a non-greedy match for the content but need to handle nested braces if they were a thing.
    # In these examples, they aren't.
    patterns = {
        'S': rf'S{name}\s*=\s*({{.*?}})',
        'I': rf'I{name}\s*=\s*({{.*?}})',
        'O': rf'O{name}\s*=\s*({{.*?}})',
        'N': rf'N{name}\s*=\s*({{.*?}})',
        'R': rf'R{name}\s*=\s*({{.*?}})'
    }
    
    for key, pattern in patterns.items():
        m = re.search(pattern, content, re.DOTALL)
        if m:
            sets[key] = parse_lean_set(m.group(1))
        else:
            raise ValueError(f"Could not find set for {key}{name}")

    # Process N (transitions) into a dict: (state, input) -> next_state
    transitions = {}
    for entry in sets['N']:
        if not isinstance(entry, tuple) or len(entry) != 2:
            # Handle the case where NZx1 = {((1, 2), 1)}
            # entry is ((1, 2), 1)
            raise ValueError(f"Invalid transition entry: {entry}")
        (state_input, next_state) = entry
        transitions[state_input] = next_state
    
    # Process R (readout) into a dict: state -> output
    readout = {}
    for entry in sets['R']:
        if not isinstance(entry, tuple) or len(entry) != 2:
            raise ValueError(f"Invalid readout entry: {entry}")
        (state, output) = entry
        readout[state] = output
        
    return WymoreSystem(name, sets['S'], sets['I'], sets['O'], transitions, readout)

if __name__ == "__main__":
    import sys
    if len(sys.argv) > 1:
        with open(sys.argv[1], 'r') as f:
            content = f.read()
            system = parse_wymore_system(content)
            print(system)
            print("Transitions:", system.transitions)
            print("Readout:", system.readout)
