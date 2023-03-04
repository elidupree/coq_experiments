import sys
import matplotlib.pyplot as plt

data = [int(line) for line in sys.stdin]
plt.scatter(range(len(data)), data)
# plt.xscale("log")
# plt.yscale("log")
plt.show()