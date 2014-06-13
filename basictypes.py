from z3 import *;
init("libz3.so");


#*************************************************************
#Basic definitions
#*************************************************************

Entity = DeclareSort('Entity');
ego = Const('ego', Entity);
Resource = DeclareSort('Resource');
Time = RealSort();

inArea = Function('inArea', Entity, BoolSort());


#Basic types
MsgType, (Req, Ack) = EnumSort('MsgType', ('Req', 'Ack'));
Message = DeclareSort('Message');


Location, (farAway, close, inInter, passed) = EnumSort('Location', ('farAway', 'close', 'inInter', 'passed'));
Acceleration, (const, incr, decr) = EnumSort('Acceleration', ('const', 'incr', 'decr'));

SystemState = Datatype('SystemState')
SystemState.declare('mkstate', 
                    ('time', Time),
                    ('loc', Location),
                    ('egopos', RealSort()),
                    ('speed', RealSort()),
                    ('targetSpeed', RealSort()),
                    ('delay', BoolSort()),
                    ('req', Message),
                    ('willEnter', BoolSort()),
                    ('ltnw', RealSort()),
                    ('acc', Acceleration));

SystemState = SystemState.create();                    

time = SystemState.time;
loc = SystemState.loc;
speed = SystemState.speed;
targetSpeed = SystemState.targetSpeed;
acc = SystemState.acc;
delay = SystemState.delay;
willEnter = SystemState.willEnter;
egopos = SystemState.egopos;
req = SystemState.req;
ltnw = SystemState.ltnw; #Last Time Not Waiting

pos = Function('pos', Entity, SystemState, RealSort());
