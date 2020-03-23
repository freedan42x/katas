class Machine:
  def __init__(self):
    self.cmd_ix = 0

  def command(self, cmd, num):
    return ACTIONS()[self.cmd_ix](num)

  def response(self, res):
    if not res:
      self.cmd_ix += 1
