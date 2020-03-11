import csv

binary_functions = []
source_functions = []
binary_diff = []
ghidra_functions = []
ghidra_radare_diff = []

with open("binary_function_list.csv", "r") as binary:
    x = csv.reader(binary)
    for line in x:
        binary_functions.append(line)
        # x = binary.readline()
    binary.close()

with open("source_function_list.csv", "r") as source:
    x = csv.reader(source)
    for line in x:
        source_functions.append(line)
        # x = source.readline()
    source.close()

with open("ghidra_function_names.csv", "r") as ghidra:
    x = csv.reader(ghidra)
    for line in x:
        ghidra_functions.append(line)
    ghidra.close()

intersection = []
diff = []
source_only = []
arch_specific = []
dup_source = []

# Find all functions that are in both the binary and source
# also find functions that are only in the binary
for s in binary_functions:
    if s in source_functions:
        intersection.append(s)
    else:
        diff.append(s)

# Find all functions that are only in the source code
for s in source_functions:
    if s not in binary_functions:
        source_only.append(s)

# Find the architecture specific functions that are being used in xinu
for s in binary_functions:
    if source_functions.count(s) > 1:
        arch_specific.append(s)

# Find all functions that ghidra found but radare did not find
for s in ghidra_functions:
    if s not in binary_functions:
        ghidra_radare_diff.append(s)

for s in source_only:
    if source_only.count(s) > 1:
        if s not in dup_source:
            dup_source.append(s)

print("Intersection: " + str(len(intersection)))
print("Compiler Added: " + str(len(diff)))
print("Source Only: "+str(len(source_only)))
print("Ghidra Found: " + str(len(ghidra_radare_diff)))
print("Architecture Specific Functions: "+str(len(dup_source)))
print("Architecture Specific Functions Used In Xinu: "+str(len(arch_specific)))

# all_found = []
# for s in source_only:
#     all_found.append(s)
# for s in diff:
#     all_found.append(s)
# for s in intersection:
#     all_found.append(s)

# print(len(all_found))

# temp = []
# for s in source_functions:
#     if s not in temp:
#         temp.append(s)

# print("Temp: " + str(len(temp)))

# temp2 = []
# for s in temp:
#     if s not in binary_functions:
#         temp2.append(s)
# print(len(temp2))
# for s in all_found:
#     if source_functions.count(s) > 1:
#         if s not in dup_source:
#             dup_source.append(s)

with open("binary_intersect_source_functions.csv", "w") as w:
    y = csv.writer(w)
    y.writerows(intersection)
    w.close()

with open("compiler_functions.csv", "w") as d: 
    z = csv.writer(d)
    z.writerows(diff)
    d.close()

with open("source_only_functions.csv", "w") as d: 
    z = csv.writer(d)
    z.writerows(source_only)
    d.close()

with open("ghidra_found_functions.csv", "w") as d: 
    z = csv.writer(d)
    z.writerows(ghidra_radare_diff)
    d.close()

with open("arch_specific_functions.csv", "w") as d: 
    z = csv.writer(d)
    z.writerows(arch_specific)
    d.close()

with open("arch_specific_not_used_functions.csv", "w") as d: 
    z = csv.writer(d)
    z.writerows(dup_source)
    d.close()