class SimTime:
    def __init__(self):
        self.realtime = 0
        self.simtime = 0
        self.simspeed = 1

    def get(self):
        return self.simtime

    def set_speed(self, simspeed):
        self.simspeed = simspeed

    def update(self, realtime):
        delta = realtime - self.realtime
        assert delta >= 0
        
        self.simtime += self.simspeed * delta
        self.realtime = realtime
