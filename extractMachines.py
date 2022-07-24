import argparse 

parser = argparse.ArgumentParser(
    description="extract the machineNotation lines from a text file")
parser.add_argument("input_filename")
parser.add_argument("output_filename")

args = parser.parse_args()
in_fn = args.input_filename
out_fn = args.output_filename

all_file_contents = list(open(in_fn).readlines())
unproven_indices = [(i,s) for i, s in enumerate(all_file_contents) if "unproven" in s]
assert len(unproven_indices) == 1, unproven_indices
print("found line:", unproven_indices[0])
start_index = unproven_indices[0][0]
rel_file_contents = all_file_contents[start_index+1:]
all_machine_lines = [s for s in rel_file_contents if ' ' not in s]
print(f"found {len(all_machine_lines)} machines")
with open(out_fn, "w") as out_f:
    out_f.write(''.join(all_machine_lines))
