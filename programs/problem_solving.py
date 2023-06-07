import sys
import time
import itertools
from itertools import accumulate, product, permutations, combinations
import collections
from collections import Counter, OrderedDict, deque, defaultdict, ChainMap
from functools import lru_cache
import math
from math import sqrt, sin, cos, tan, ceil, fabs, floor, gcd, exp, log, log2
import fractions
from typing import List, Tuple
import numpy as np
import random
import heapq
# given a list of lists representing the cost of building a road between any two cities, and a list representing the cost of building an airport in a city, return a new cost matrix with a new node corresponding to the sky.
def sky_city_cost(city_road_cost, city_airport_cost):
    sky_cost = [[0] * (len(city_road_cost) + 1) for _ in range(len(city_road_cost) + 1)]
    for i in range(len(city_road_cost)):
        for j in range(len(city_road_cost)):
            sky_cost[i][j] = city_road_cost[i][j]
            sky_cost[i][-1] = city_airport_cost[i]
            sky_cost[-1][j] = city_airport_cost[j]
    return sky_cost

# given a list of lists representing the cost of each edge, return an adjacency matrix corresponding to the minimum spanning true.
def minimum_spanning_tree(cost_matrix):
    # initialize adjacency matrix
    adjacency_matrix = [[0 for x in range(len(cost_matrix))] for y in range(len(cost_matrix))]
    # initialize list of visited nodes
    visited = [False for x in range(len(cost_matrix))]
    # keep track of number of edges in tree
    num_edges = 0
    # start at node 0
    visited[0] = True
    # while the number of edges is less than the number of nodes - 1
    while num_edges < len(cost_matrix) - 1:
        # find the minimum cost edge
        min_cost = float("inf")
        min_x = -1
        min_y = -1
        for x in range(len(cost_matrix)):
            for y in range(len(cost_matrix)):
                if visited[x] and not visited[y] and cost_matrix[x][y] < min_cost:
                    min_cost = cost_matrix[x][y]
                    min_x = x
                    min_y = y
        # add the edge to the tree
        adjacency_matrix[min_x][min_y] = 1
        adjacency_matrix[min_y][min_x] = 1
        visited[min_y] = True
        num_edges += 1
    return adjacency_matrix

# given a list of lists representing an adjacency matrix, return a list of the nodes connected to the final node. However, if only one node is connected to the final node, return an empty list.
def final_node_connectors(adjacency_matrix):
    last_node_index = len(adjacency_matrix[0]) - 1
    last_row = adjacency_matrix[last_node_index]
    connected_nodes = []
    for i in range(len(last_row)):
        if last_row[i] == 1 and i != last_node_index:
            connected_nodes.append(i)
    if len(connected_nodes) == 1:
        return []
    else:
        return connected_nodes

# given a matrix representing the cost of building a road between any two cities, and a list representing the cost of building an airport in a city (where any two cities with airports are connected), return a list of the cities that should have airports built in them to minimize the total cost of building roads and airports such that all cities are connected. The list should be sorted in ascending order.
def select_airport_cities(city_road_cost, city_airport_cost):
  cost_matrix = sky_city_cost(city_road_cost, city_airport_cost)
  mst = minimum_spanning_tree(cost_matrix)
  final_connectors = final_node_connectors(mst)
  final_connectors.sort()
  return final_connectors

assert repr(str(select_airport_cities([[0,3,3],[3,0,3],[3,3,0]],[0,0,0]))) == repr(str([0,1,2])) or (select_airport_cities([[0,3,3],[3,0,3],[3,3,0]],[0,0,0]) == [0,1,2])
assert repr(str(select_airport_cities([[0,3,3],[3,0,3],[3,3,0]],[10,10,10]))) == repr(str([])) or (select_airport_cities([[0,3,3],[3,0,3],[3,3,0]],[10,10,10]) == [])
assert repr(str(select_airport_cities([[0,10,3],[10,0,11],[3,11,0]],[1,4,5]))) == repr(str([0,1])) or (select_airport_cities([[0,10,3],[10,0,11],[3,11,0]],[1,4,5]) == [0,1])

assert repr(str(sky_city_cost([[1,2,3],[1,2,3],[1,2,3]],[4,5,6]))) == repr(str([[1,2,3,4],[1,2,3,5],[1,2,3,6],[4,5,6,0]])) or (sky_city_cost([[1,2,3],[1,2,3],[1,2,3]],[4,5,6]) == [[1,2,3,4],[1,2,3,5],[1,2,3,6],[4,5,6,0]])

assert repr(str(minimum_spanning_tree([[0,1,3,4],[1,0,2,100],[3,2,0,5],[4,100,5,0]]))) == repr(str([[0,1,0,1],[1,0,1,0],[0,1,0,0],[1,0,0,0]])) or (minimum_spanning_tree([[0,1,3,4],[1,0,2,100],[3,2,0,5],[4,100,5,0]]) == [[0,1,0,1],[1,0,1,0],[0,1,0,0],[1,0,0,0]])

assert repr(str(final_node_connectors([[0,1,0,1],[1,0,1,0],[0,1,0,0],[1,0,0,0]]))) == repr(str([])) or (final_node_connectors([[0,1,0,1],[1,0,1,0],[0,1,0,0],[1,0,0,0]]) == [])
assert repr(str(final_node_connectors([[0,1,0,1],[1,0,1,0],[0,1,0,1],[1,0,1,0]]))) == repr(str([0,2])) or (final_node_connectors([[0,1,0,1],[1,0,1,0],[0,1,0,1],[1,0,1,0]]) == [0,2])
