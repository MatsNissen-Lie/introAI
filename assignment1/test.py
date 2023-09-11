
from queue import PriorityQueue
import time


frontier = PriorityQueue()


def add(priority, item):
    frontier.put((priority, item))


nums = list(range(1, 1000))
nums.reverse()

for i in nums:
    add(i, i)

low = frontier.get()
print("low", low)
