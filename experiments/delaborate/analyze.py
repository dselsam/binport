import csv
import collections
import argparse

parser = argparse.ArgumentParser()
parser.add_argument('filename', action='store', type=str)
args = parser.parse_args()

n_types      = 0
n_values     = 0
type_totals  = collections.defaultdict(int)
value_totals = collections.defaultdict(int)

with open(args.filename) as csvfile:
    reader = csv.reader(csvfile, delimiter=' ', quotechar='|')
    for row in reader:
        if len(row) < 3: continue
        clsName, inType, result = row[0], row[1], row[2]
        if inType == "true":
            n_types += 1
            type_totals[result] += 1
        else:
            n_values += 1
            value_totals[result] += 1

if n_types > 0:            
    print("-------Types---")
    print("Total: (%d / %d) = %0.2f" % (type_totals["success"], n_types, type_totals["success"] / n_types))
    for status, total in type_totals.items():
        print("  %16s: %3d (%0.2f)" % (status, total, total / n_types))

if n_values > 0:
    print("-------Values---")
    print("Total: (%d / %d) = %0.2f" % (value_totals["success"], n_values, value_totals["success"] / n_values))
    for status, total in value_totals.items():
        print("  %16s: %3d (%0.2f)" % (status, total, total / n_values))
