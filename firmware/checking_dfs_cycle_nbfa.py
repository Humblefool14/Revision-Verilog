from typing import List, Set, Tuple

class State:
    def __init__(self, id: int, is_initial: bool = False, is_accepting: bool = False):
        self.id = id
        self.is_initial = is_initial
        self.is_accepting = is_accepting
        self.transitions: List[State] = []

class NBA:
    def __init__(self):
        self.states: List[State] = []

    def add_state(self, state: State):
        self.states.append(state)

    def add_transition(self, from_state: State, to_state: State):
        from_state.transitions.append(to_state)

def nested_dfs(nba: NBA) -> bool:
    def dfs_blue(state: State, blue: Set[int], red: Set[int]) -> bool:
        blue.add(state.id)
        
        for next_state in state.transitions:
            if next_state.id not in blue:
                if dfs_blue(next_state, blue, red):
                    return True
            elif next_state.id not in red:
                if dfs_red(next_state, set(), red):
                    return True
        
        blue.remove(state.id)
        return False

    def dfs_red(state: State, stack: Set[int], red: Set[int]) -> bool:
        stack.add(state.id)
        red.add(state.id)
        
        for next_state in state.transitions:
            if next_state.id in stack:
                if next_state.is_accepting:
                    return True
            elif next_state.id not in red:
                if dfs_red(next_state, stack, red):
                    return True
        
        stack.remove(state.id)
        return False

    blue: Set[int] = set()
    red: Set[int] = set()

    for state in nba.states:
        if state.is_initial and state.id not in blue:
            if dfs_blue(state, blue, red):
                return False  # NBA is not empty

    return True  # NBA is empty

# Example usage
nba = NBA()

# Create states
s0 = State(0, is_initial=True)
s1 = State(1)
s2 = State(2, is_accepting=True)

# Add states to NBA
nba.add_state(s0)
nba.add_state(s1)
nba.add_state(s2)

# Add transitions
nba.add_transition(s0, s1)
nba.add_transition(s1, s2)
nba.add_transition(s2, s1)

# Check emptiness
is_empty = nested_dfs(nba)
print(f"Is NBA empty? {is_empty}")