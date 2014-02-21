import string
from functools import * 
try:
    import gv
except:
    print('Graphviz with python support not installed, graph drawing functionality can not be used.')

font = "Bookman-LightItalic"
font = "Georgia"

class Infix:
    def __init__(self, function):
        self.function = function
    def __ror__(self, other):
        return Infix(lambda x, self=self, other=other: self.function(other, x))
    def __or__(self, other):
        return self.function(other)
    def __rlshift__(self, other):
        return Infix(lambda x, self=self, other=other: self.function(other, x))
    def __rshift__(self, other):
        return self.function(other)
    def __call__(self, value1, value2):
        return self.function(value1, value2)

# Output related classes
class GraphPrinter:
    def relationString(self, player=None, map=None):
        if(map==None):
            map = {}
            for i in range(len(self.worlds)): map[self.worlds[i]] = i
        if(player==None):
            return string.join([self.relationString(p, map) for p in range(len(self.relations))], "")
        else:
            return string.join(["  - relation[%d]: %d -> %d\n" % (player, map[v], map[w]) for (v,w) in self.relations[player]], "")


class GraphDrawer:
    def setProps(self, key, props):
        for (name, prop) in props:
                gv.setv(key, name, prop)
    
    def getPlayers(self, v, w): return [p for p in range(len(self.relations)) if (v,w) in self.relations[p]]        

    def createLegend(self, filename, colorMap, styleMap):
        legend = gv.digraph("legend")
        gv.setv(legend, "overlap", "true")
        c=0
        for i in colorMap:
            key = gv.node(legend, "%d-from" % c)
            key2 = gv.node(legend, "%d-to" % c)
            self.setProps(key,  [("color", colorMap[i]), ("fixedsize", "true"), ("height", "0.03"), ("width", "0.03"), ("label", ""), ("pin", "true"), ("pos", "1,%f!" % (1+0.5*c))])
            self.setProps(key2, [("color", colorMap[i]), ("fixedsize", "true"), ("height", "0.03"), ("width", "0.03"), ("label", ""), ("pin", "true"), ("pos", "2,%f!" % (1+0.5*c))])
            ed = gv.edge(key, key2)
            self.setProps(ed, [("style", styleMap[i]), ("color", colorMap[i]), ("label", string.join([str(ii) for ii in list(i)], ","))])
            c=c+1
        gv.setv(legend, 'fontname', font)
        gv.layout(legend,'neato')
        #gv.render(legend,'eps', "%s-legend.eps" % filename)
        gv.render(legend,'png', "%s-legend.png" % filename)
    
    def drawOneGraph(self, filename):
        self.spacify()
        isDone=[]
        colors = ["red", "blue", "blue4", "orange", "green", "purple", "pink", "black" , "goldenrod", "chocolate4", "chartreuse"]
        styles = ["dashed", "solid", "dashed", "solid", "dashed", "solid", "dashed", "solid", "dashed", "solid", "dashed", "solid"]
        cidx=0;
        colorMap={}
        styleMap={}
        G = gv.digraph("kripke model")
        
        nodeMap = {}
        for w in self.worlds:
            nodeMap[w] = gv.node(G, w.nodeName())
            self.setProps(nodeMap[w], [("fontname",font), ("style", "filled")])
        
        for v in self.worlds:
            for w in self.worlds:
                if((v,w) in isDone): continue
                isDone.append((v,w))
                players = self.getPlayers(v,w)
                if len(players) == 0: continue
                if(tuple(players) in colorMap):
                    color = colorMap[tuple(players)]
                    style = styleMap[tuple(players)]
                else:
                    color = colors[cidx]
                    style = styles[cidx]
                    cidx = cidx+1
                    colorMap[tuple(players)] = color
                    styleMap[tuple(players)] = style
                key = gv.edge(nodeMap[v], nodeMap[w])
                #lab = string.join([str(p) for p in players], "")
                #self.setProps(key, [("label", lab)])
                self.setProps(key, [("fontname",font), ("style", "filled"), ("style", style), ("color", color)])
                if(players == self.getPlayers(w,v)):
                    isDone.append((w,v))
                    self.setProps(key, [("dir","both")])
        self.createLegend(filename, colorMap, styleMap)
        gv.setv(G, 'fontname', "sans-serif")
        gv.layout(G,'circo')
        #gv.render(G,'eps', "%s.eps" % filename)
        gv.render(G,'png', "%s.png" % filename)


# States in different types of kripke models
class State:
	def isAdjacent(self, player, w):
		return (w in self.adjacent[player])

class World(State):
  def __init__(self, werewolf, model):
      self.werewolf, self.model = (werewolf, model)
      self.spaces=0
  def isConsistent(self, precondition):  return precondition.isConsistent(self)
  def duplicate(self):                   return World(self.werewolf, self.model)
  def __str__(self):                     return "player %d is the werewolf" % self.werewolf
  def nodeName(self):                    return "w%d%s" % (self.werewolf, " "*self.spaces)

# Action Model States
class Precondition(State):
  def __init__(self, isWerewolf, player, model, label):
      self.isWerewolf, self.player, self.model, self.label = (isWerewolf, player, model, label)
  def isConsistent(self, world): return (self.player == world.werewolf) == self.isWerewolf
  def __str__(self):             return self.label
  def nodeName(self):            return self.label
  def __call__(self, s):         return self.isConsistent(s)

class TruePrecondition(State):
    def isConsistent(self, world):
        return True
    def __str__(self):  return "T"
    def nodeName(self): return "T"

# Model
class Model(GraphPrinter, GraphDrawer):
    def spacify(self):
        spaceMap = {}
        for (i,w) in enumerate(self.worlds):
            if not w.nodeName() in spaceMap: spaceMap[w.nodeName()] = 0
            else: spaceMap[w.nodeName()] = spaceMap[w.nodeName()]+1;
            w.spaces=spaceMap[w.nodeName()]
    def K(self, player, expr, world=None):
        if(world==True):
            return reduce(lambda x,y: x and y,  [self.K(player,expr,w) for w in self.worlds])
        if world==None: return partial(self.K, player, expr)
        return reduce(lambda x,y: x and y, [True] + [expr(w) for (v,w) in self.relations[player] if v==world])
    
    def M(self, player, expr, world=None):
        if(world==True): return reduce(lambda x,y: x and y,  [self.M(player,expr,w) for w in self.worlds])
        if world==None: return partial(self.M, player, expr)
        return reduce(lambda x,y: x or y,  [False] + [expr(w) for (v,w) in self.relations[player] if v==world])
        
    def isReflexive(self, player):
        return reduce(lambda x,y: x and y, [(x,x) in self.relations[player] for x in self.worlds ])
    def isSymmetric(self, player):
        return reduce(lambda x,y: x and y, [(x,y) in self.relations[player] for (y,x) in self.relations[player]])
    def isTransitive(self, player):
        return reduce(lambda x,y: x and y, [(r,u) in self.relations[player] for (r,s) in self.relations[player] for (t,u) in self.relations[player] if s==t])
    
    def isS5(self, player=None):
        if player==None: return [self.isS5(p) for p in range(len(self.relations))]
        else: return self.isReflexive(player) and self.isSymmetric(player) and self.isTransitive(player)

    def fullyConnectedRelation(self):
        return [(w1,w2) for w1 in self.worlds for w2 in self.worlds]
    def reflexiveRelation(self):
        return [(w1,w1) for w1 in self.worlds]
    
    def initializeAdjacency(self):
        for w in self.worlds: w.adjacent = [[] for i in range(len(self.relations))]
        for r in range(len(self.relations)):
            for (w1, w2) in self.relations[r]: w1.adjacent[r].append(w2)

    def filterGameWorlds(self):
        worldMap, worlds = ({}, [])
        for (game, action) in self.worlds:
            newGameWorld = game.duplicate()
            worldMap[(game, action)] = newGameWorld
            worlds.append(newGameWorld)
        self.worlds = worlds
        self.relations = [ [(worldMap[(w1game, w1act)], worldMap[(w2game, w2act)]) for ((w1game,w1act),(w2game,w2act)) in rel ] for rel in self.relations]
        
    def consistentRelation(self, player):
        return [((w1game, w1act), (w2game, w2act)) for (w1game, w1act) in self.worlds for (w2game, w2act) in self.worlds if w1game.isAdjacent(player, w2game) and w1act.isAdjacent(player, w2act)]

# Game Model
class GameModel(Model):
    def ww(self, player): return Precondition(True, player, self, "w%d" % player)
    def notww(self, player): return Precondition(False, player, self, "not w%d" % player)
    
    def __init__(self, n=None):
        if n!=None:
            self.worlds    = [World(i, self) for i in range(n)]
            self.relations = [self.fullyConnectedRelation() for player in range(n)]
            self.initializeAdjacency()

    def __mul__(self, other):
        if(len(self.relations)!=len(other.relations)): raise Exception("The game model has %d agents, whereas the action model has %d agents. Both should have the same number of agents" % (len(self.relations), len(other.relations)))
        result = GameModel()
        result.worlds = [(w1, w2) for w1 in self.worlds for w2 in other.worlds if w1.isConsistent(w2)]
        result.relations = [ result.consistentRelation(player) for player in range(len(self.relations))]
        #result.relations = []
        result.filterGameWorlds()
        result.initializeAdjacency()
        return result

    def __str__(self):
        w = string.join([" - world[%d]: %s\n" % (i, ("(%s, %s)" % (self.worlds[i][0].__str__(), self.worlds[i][1].__str__())) if type(self.worlds[i]) == tuple else self.worlds[i].__str__()) for i in range(len(self.worlds))], "")
        return "GameModel\n%s\n - relations:\n%s\n" % (w, self.relationString())


# Update models
class ActionModel(Model):
    def __str__(self):
        w = ("%s"*len(self.worlds)) % tuple([" - world[%d]: %s\n" % (i, self.worlds[i].__str__()) for i in range(len(self.worlds))])
        return "ActionModel\n%s\n%s\n" % (w, self.relationString())

class TurnCard(ActionModel):
	def __init__(self, player, n):
		self.worlds = [Precondition(False,player,self,"HumanCard%d" % player), Precondition(True,player,self,"WerewolfCard%d" % player)]
		self.relations = [ (self.reflexiveRelation() if player == p else self.fullyConnectedRelation()) for p in range(n)]
		self.initializeAdjacency()

class NightKilling(ActionModel):
	def __init__(self, player, n, isWerewolf):
		self.worlds = [Precondition(isWerewolf,player,self, "DeathOfWerewolf%d" % player if isWerewolf else "DeathOfHuman%d" % player)]
		self.relations = [self.reflexiveRelation() for p in range(n)]
		self.initializeAdjacency()

class QuizMasterSlipsQuitly(ActionModel):
	def __init__(self, receiver, player, n, isWerewolf):
		truth = TruePrecondition()
		message = Precondition(isWerewolf, player, self, "%sWerewolf%d" % ("" if isWerewolf else "not", player))
		self.worlds = [truth, message]
		self.relations = [([(message, message), (truth, truth)] if receiver == p else [(message, truth), (truth, truth)]) for p in range(n)]
		self.initializeAdjacency()

class QuizMasterSlip(ActionModel):
    def __init__(self, receiver, n):
        truth = TruePrecondition()
        messages = [truth] + [Precondition(False, p, self, "notWerewolf%d" % p) for p in range(n) if p is not receiver]
        self.worlds = messages
        self.relations = [(self.reflexiveRelation() if p == receiver else self.fullyConnectedRelation()) for p in range(n)]
        self.initializeAdjacency()

class DayKilling(ActionModel):
	def __init__(self, player, n):
		self.worlds = [Precondition(True,player,self,"DeathOfWerewolf%d" % player),Precondition(False,player,self,"DeathOfHuman%d" % player)]
		self.relations = [self.reflexiveRelation() for p in range(n)]
		self.initializeAdjacency()

itholdsthat = Infix(lambda w,f: f(w))
def knot(f): return (lambda x: not(f(x)))

def regarding(game):
    global K,M,ww,notww,kor,kand
    def K(player, expr, world=None): return game.K(player, expr, world)
    def M(player, expr, world=None): return game.M(player, expr, world)
    def ww(player): return game.ww(player)
    def notww(player): return game.notww(player)
    kor = Infix(lambda f,g: (lambda x: reduce(lambda x,y: x and y, [(f(w) or g(w)) for w in game.worlds]) if(x==True) else f(x) or g(x)))
    kand = Infix(lambda f,g: (lambda x: reduce(lambda x,y: x and y, [(f(w) and g(w)) for w in game.worlds]) if(x==True) else f(x) and g(x)))

def pp(x): return "yes" if x else "no"

def printDraws(game = None, players = 4):
    game = GameModel(players) if game==None else game
    game.drawOneGraph("game-initial")    
    for player in range(players):
        action = TurnCard(player, players)
        game = game * action
        action.drawOneGraph("game-after-%d-draws-action" % (player+1))
        game.drawOneGraph("game-after-%d-draws" % (player+1))
    return game
    
def printActions(game, players):
    action = NightKilling(2, players, False)
    game = game * action
    action.drawOneGraph("game-after-one-death-action")
    game.drawOneGraph("game-after-one-death")
    action = QuizMasterSlip(0, players)
    game = game * action
    action.drawOneGraph("game-after-one-leak-action")
    game.drawOneGraph("game-after-one-leak")
    action = DayKilling(1, players)
    game = game * action
    action.drawOneGraph("game-after-second-death-action")
    game.drawOneGraph("game-after-second-death")

def main():
    #game = printDraws()
    #game = printActions(game, 4)    
    
    players = 4;
    game = GameModel(players)
    regarding(game)
    for p0 in range(players):
        v= True <<itholdsthat>> K(p0, ww(0) <<kor>> ww(1) <<kor>> ww(2) <<kor>> ww(3))
        print("Does player %d know that there is a werewolf? %s"  % (p0, pp(v)))
    
    for player in range(players): game = game * TurnCard(player, players)
    #regarding(game)    
    #for p0 in range(players):
    #    v = True <<itholdsthat>> (K(p0, ww(p0)) <<kor>> K(p0, notww(p0)))
    #    print "Is player %d creature aware?"  % p0, pp(v)
    #    for p1 in range(players):
    #        v = True <<itholdsthat>> K(p0, (K(p1, ww(p1)) <<kor>> K(p1, notww(p1))))
    #        print " - Does player %d know that player %d is creature aware?"  % (p1, p0), pp(v)

    #print "Considering this worlds: %s" % game.worlds[2]
    #for p0 in range(players):
    #    v= True <<itholdsthat>> (K(p0, ww(0)) <<kor>> K(p0, ww(1)) <<kor>> K(p0, ww(2)) <<kor>> K(p0, ww(3)))
    #    v= game.worlds[2] <<itholdsthat>> (K(p0, ww(0)) <<kor>> K(p0, ww(1)) <<kor>> K(p0, ww(2)) <<kor>> K(p0, ww(3)))
    #    print " - Does player %d know who the werewolf is?"  % p0, pp(v)
    
    game.drawOneGraph("game-before-quit-slip")
    print("Is the game S5 before updating? %s" % (pp(reduce(lambda x,y: x and y, game.isS5()))))
    action = QuizMasterSlipsQuitly(0,1,players,True)
    print("Is the action S5? %s" % (pp(reduce(lambda x,y: x and y, action.isS5()))))
    game = game*action
    print("Is the game S5 after updating? %s" % (pp(reduce(lambda x,y: x and y, game.isS5()))))
    action.drawOneGraph("quit-slip-action")
    game.drawOneGraph("game-after-quit-slip")
    regarding(game)
    print("Considering world: %s" % game.worlds[0])
    for p0 in range(players):
        v = game.worlds[0] <<itholdsthat>> (K(p0, ww(0)) <<kor>> K(p0, ww(1)) <<kor>> K(p0, ww(2)) <<kor>> K(p0, ww(3)))
        print("Does player %d know who the werewolf is? %s"  % (p0, pp(v)))
    for p1 in range(players):
        v = game.worlds[0] <<itholdsthat>> knot(K(p1, K(0, ww(0)) <<kor>> K(0, ww(1)) <<kor>> K(0, ww(2)) <<kor>> K(0, ww(3))))
        print("Does player %d know that player %d does not know who the werewolf is? %s"  % (p1, 0, pp(v)))

if __name__ == "__main__":
    main()
