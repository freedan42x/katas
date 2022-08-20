from typing import *


DIRS = {
    '^': (-1, 0),
    '>': (0, 1),
    'v': (1, 0),
    '<': (0, -1)
}

ENEMIES = {
    'E': 2,
    'D': 3
}


class MapState:
    def __init__(self, field: List[List[str]]):
        self.field = field
        self.width = len(field)
        self.height = len(field[0])

        self.merchants = {}
        for x in range(self.width):
            for y in range(self.height):
                c = self.field[x][y]

                if c == 'M':
                    self.merchants[x, y] = 3

                elif c in DIRS:
                    self.player_pos = (x, y)
                    self.player_dir = c

        self.demonlord_hp = 10


    def getpos_at_dir(self, direction: str) -> Optional[Tuple[int, int]]:
        dx, dy = DIRS.get(direction)
        old_x, old_y = self.player_pos

        x = old_x + dx
        y = old_y + dy

        if x >= 0 and x < self.width and y >= 0 and y < self.height:
            return x, y

        return None


    def getpos_infront(self) -> Optional[Tuple[int, int]]:
        return self.getpos_at_dir(self.player_dir)


    def get_infront(self) -> Optional[str]:
        if pos := self.getpos_infront():
            x, y = pos
            return self.field[x][y]

        return None


    def set_at(self, pos: Tuple[int, int], c: str):
        x, y = pos
        self.field[x][y] = c


    def set_at_cur(self, c: str):
        self.set_at(self.player_pos, c)


class Player:
    def __init__(self, map_state: MapState):
        self.map_state = map_state
        self.MAX_HP = 3
        self.HP = 3
        self.BASE_ATK = 1
        self.ATK = 1
        self.DEF = 1
        self.coins = 0
        self.keys = 0
        self.health_potions = 0
        self.enemy_kills = 0


    def calc_dmg_taken(self, enemy_atk) -> int:
        return max(0, enemy_atk - self.DEF)


    def calc_atk(self):
        self.ATK = self.BASE_ATK + self.enemy_kills // 3


    def consider_enemies_around(self) -> bool:
        for d in DIRS:
            if p := self.map_state.getpos_at_dir(d):
                x, y = p

                if (c := self.map_state.field[x][y]) in ENEMIES:
                    self.HP -= self.calc_dmg_taken(ENEMIES[c])

        return self.HP > 0


    def move_forward(self) -> bool:
        if pos := self.map_state.getpos_infront():
            c = self.map_state.get_infront()

            if c == ' ':
                pass
            elif c == 'C':
                self.coins += 1
            elif c == 'K':
                self.keys += 1
            elif c == 'H':
                self.health_potions += 1
            elif c == 'S':
                self.DEF += 1
            elif c == 'X':
                self.BASE_ATK += 1
                self.calc_atk()
            else:
                return False
            
            if not self.consider_enemies_around(): return False

            self.map_state.set_at_cur(' ')
            self.map_state.set_at(pos, self.map_state.player_dir)
            self.map_state.player_pos = pos

            return True
        
        return False


    def change_direction(self, d: str) -> bool:
        self.map_state.set_at_cur(d)
        self.map_state.player_dir = d

        return self.consider_enemies_around()


    def attack_enemy(self) -> bool:
        if (pos := self.map_state.getpos_infront()) and (e := self.map_state.get_infront()) in ENEMIES:
            if e == 'E':
                self.map_state.set_at(pos, ' ')
                self.enemy_kills += 1
                self.calc_atk()
            else:
                self.map_state.demonlord_hp -= self.ATK

                if self.map_state.demonlord_hp <= 0:
                    self.map_state.set_at(pos, ' ')

            return self.consider_enemies_around()

        return False


    def use_coin(self) -> bool:
        if self.coins == 0: return False

        if (pos := self.map_state.getpos_infront()) and self.map_state.get_infront() == 'M':
            self.map_state.merchants[pos] -= 1
            self.coins -= 1

            if self.map_state.merchants[pos] == 0:
                del self.map_state.merchants[pos]
                self.map_state.set_at(pos, ' ')

            return True

        return False


    def use_key(self) -> bool:
        if self.keys == 0: return False

        if (pos := self.map_state.getpos_infront()) and self.map_state.get_infront() in '-|':
            self.keys -= 1
            self.map_state.set_at(pos, ' ')

            return True
            
        return False


    def use_health_potion(self) -> bool:
        if self.health_potions == 0: return False
        if self.HP == self.MAX_HP: return False

        self.HP = self.MAX_HP
        self.health_potions -= 1

        return self.consider_enemies_around()


    def make_bag(self) -> List[str]:
        return list('C' * self.coins + 'H' * self.health_potions + 'K' * self.keys)


def rpg(field: List[List[str]], actions: List[str]) -> Tuple[List[List[str]], int, int, int, List[str]]:
    player = Player(MapState(field))

    for action in actions:
        if action == 'F':
            if not player.move_forward():
                return None

        elif action in DIRS:
            player.change_direction(action)

        elif action == 'A':
            if not player.attack_enemy():
                return None

        elif action == 'C':
            if not player.use_coin():
                return None

        elif action == 'K':
            if not player.use_key():
                return None

        elif action == 'H':
            if not player.use_health_potion():
                return None

        else:
            return None

    return (player.map_state.field, player.HP, player.ATK, player.DEF, player.make_bag())


m = [list(l) for l in ['SX#  EDE',
                       '  # EEEEE',
                       '#-#     X',
                       '         ',
                       '^       K']]
