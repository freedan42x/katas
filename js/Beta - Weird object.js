class T {
  constructor(prop=0, step=1) {
    this._prop = prop
    this.step = step
  }
  
  get prop() {
    this._prop += this.step
    return this._prop
  }
  
  set prop(step) {
    this.step = step
  }
}

const newWeirdObject = () => new T()
