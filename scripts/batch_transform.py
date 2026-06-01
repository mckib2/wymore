import os
import glob
from scxml_transformer import system_to_scxml
from parser import parse_wymore_system

def batch_transform(input_dir, output_dir):
    if not os.path.exists(output_dir):
        os.makedirs(output_dir)
    
    lean_files = glob.glob(os.path.join(input_dir, "*.lean"))
    for lean_file in lean_files:
        try:
            with open(lean_file, 'r') as f:
                content = f.read()
                system = parse_wymore_system(content)
                scxml = system_to_scxml(system)
                
                base_name = os.path.splitext(os.path.basename(lean_file))[0]
                output_file = os.path.join(output_dir, f"{base_name}.scxml")
                
                with open(output_file, 'w') as out_f:
                    out_f.write(scxml)
                print(f"Transformed {lean_file} -> {output_file}")
        except Exception as e:
            print(f"Skipping {lean_file}: {e}")

if __name__ == "__main__":
    import argparse
    
    parser = argparse.ArgumentParser(description="Batch transform Lean 4 Wymore systems to SCXML.")
    parser.add_argument("-i", "--input-dir", default="Appendix3", help="Directory containing .lean files (default: Appendix3).")
    parser.add_argument("-o", "--output-dir", default="output_scxml", help="Directory to save generated SCXML files (default: output_scxml).")
    
    args = parser.parse_args()
        
    batch_transform(args.input_dir, args.output_dir)
